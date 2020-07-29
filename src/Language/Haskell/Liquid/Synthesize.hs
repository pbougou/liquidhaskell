{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Generate 
import qualified Language.Haskell.Liquid.Types.RefType as R
import           Language.Haskell.Liquid.Synthesize.Termination
import           Language.Haskell.Liquid.Synthesize.Generate
import           Language.Haskell.Liquid.Synthesize.GHC hiding (SSEnv)
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc hiding (notrace)
import           Language.Haskell.Liquid.Constraint.Fresh (trueTy)
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import           Language.Haskell.Liquid.Synthesize.Env

import           CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import           Var 
import           TyCon
import           DataCon
import           Text.PrettyPrint.HughesPJ (text, ($+$))
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict as M 
import           Data.Maybe
import           Debug.Trace 
import           Language.Haskell.Liquid.GHC.TypeRep
import           Data.List 
import           Data.Tuple.Extra
import           CoreUtils (exprType)
import           TyCoRep
import           Language.Fixpoint.Types.Visitor (mapKVars)
import           TysWiredIn

synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM go (M.toList $ holesMap cginfo)
  where 
    measures = map (val . msName) ((gsMeasures . gsData . giSpec . ghcI) cginfo)
    go (x, HoleInfo t loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          (uniVars, _) = getUniVars coreProgram topLvlBndr
          fromREnv' = filterREnv (reLocal env)
          fromREnv'' = M.fromList (filter (rmClassVars . toType . snd) (M.toList fromREnv'))
          rmClassVars t = case t of { TyConApp c _ -> not . isClassTyCon $ c; _ -> True }
          fromREnv  = M.fromList (rmMeasures (measures ++ reflects) (M.toList fromREnv''))
          isForall t = case t of { ForAllTy{} -> True; _ -> False}
          rEnvForalls = M.fromList (filter (isForall . toType . snd) (M.toList fromREnv))
          fs = map (snd . snd) $ M.toList (symbolToVar coreProgram topLvlBndr rEnvForalls)

          ssenv0 = symbolToVar coreProgram topLvlBndr fromREnv
          (senv1, foralls') = initSSEnv typeOfTopLvlBnd cginfo ssenv0
          reflects = map symbol ((gsReflects . gsRefl . giSpec . ghcI) cginfo)

          cons = map ((map dataConWorkId) . tyConDataCons . fst) $ M.toList ((tcmTyRTy . tyConInfo) cginfo)
          tys = map (map (showTy . varType)) cons
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr (reverse uniVars) M.empty
      let foralls = foralls' ++ fs
      fills <- synthesize' ctx cgi senv1 typeOfTopLvlBnd topLvlBndr typeOfTopLvlBnd foralls state0 (concat cons)

      let outMode = debugOut (getConfig cge)

      return $ ErrHole loc (
        if not (null fills)
          then text "\n Hole Fills:" $+$  if outMode 
                                            then pprintManyDebug (map fromAnf fills)
                                            else pprintMany (map (coreToHs typeOfTopLvlBnd topLvlBndr . fromAnf) fills)
          else mempty) mempty (symbol x) typeOfTopLvlBnd 


synthesize' :: SMT.Context -> CGInfo -> SSEnv -> SpecType ->  Var -> SpecType -> [Var] -> SState -> [Var] -> IO [CoreExpr]
synthesize' ctx cgi senv tx xtop ttop foralls st2 cons
 = evalSM (fixConstructors cons >> go tx) ctx senv st2
  where 
    fixConstructors :: [Var] -> SM ()
    fixConstructors cons = 
      do  cge <- sCGEnv <$> get
          ts <- liftCG $ mapM (consE cge) (map GHC.Var cons)
          mapM_ (\(v, t) -> addEnv v t) (zip cons ts)
          -- trace (" CONSTRUCTORS 2 " ++ show res) $ return undefined

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t _x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ _r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = drop 1 (argsP coreProgram xtop)
          (_, (xs, txs, _), _) = bkArrow ttop
      addEnv xtop $ decrType xtop ttop args (zip xs txs)

      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do let ts = unifyWith (toType t)
                  if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                              else modify (\s -> s { sUGoalTy = Just ts } )
                  modify (\s -> s {sForalls = (foralls, [])})
                  emem0 <- insEMem0 senv
                  modify (\s -> s { sExprMem = emem0 })
                  synthesizeBasic t

    go (RAllP _ t) = go t

    go (RRTy _env _ref _obl t) = go t

    go t@RFun{} 
         = do ys <- mapM freshVar txs
              let su = F.mkSubst $ zip xs (EVar . symbol <$> ys) 
              mapM_ (uncurry addEnv) (zip ys ((subst su)<$> txs)) 
              let dt = decrType xtop ttop ys (zip xs txs)
              addEnv xtop dt 
              mapM_ (uncurry addEmem) (zip ys (subst su <$> txs)) 
              addEmem xtop dt
              senv1 <- getSEnv
              let goalType = subst su to
                  hsGoalTy = toType goalType 
                  ts = unifyWith hsGoalTy
              if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                          else modify (\s -> s { sUGoalTy = Just ts } )
              modify (\s -> s { sForalls = (foralls, []) } )
              emem0 <- insEMem0 senv1
              modify (\s -> s { sExprMem = emem0 })
              mapM_ (\y -> addDecrTerm y []) ys
              scruts <- synthesizeScrut ys
              modify (\s -> s { scrutinees = scruts })
              GHC.mkLams ys <$$> synthesizeBasic goalType
      where (_, (xs, txs, _), to) = bkArrow t 

    go t = error (" Unmatched t = " ++ show t)

synthesizeBasic :: SpecType -> SM [CoreExpr]
synthesizeBasic t = do
  let ts = unifyWith (toType t) -- All the types that are used for instantiation.
  if null ts  then  modify (\s -> s { sUGoalTy = Nothing } )
              else  modify (\s -> s { sUGoalTy = Just ts } )
  modify (\s -> s { sGoalTys = [] })
  fixEMem t
  fixScrutinees t
  -- HACK: If current scrutinee is boolean, case split on that first...
  scs <- scrutinees <$> get
  i <- caseIdx <$> get
  if snd3 (scs !! i) == boolTy 
    then synthesizeMatch t
    else  do  es <- genTerms t
              if null es  then synthesizeMatch t
                          else return es

fixScrutinees :: SpecType -> SM ()
fixScrutinees t = do 
  scruts' <- scrutinees <$> get
  let (x, y)   = (filter ((== (toType t)) . snd3) scruts', filter ((/= (toType t)) . snd3) scruts') 
      (y1, y2) = (filter ((== 1) . tyConFamilySize . thd3) y, filter ((/= 1) . tyConFamilySize . thd3) y)
      (y3, y4) = (filter ((== boolTyCon) . thd3) y2, filter ((/= boolTyCon) . thd3) (res1 y1 ++ y2))
      tsDataCons' x = map ((map (snd . fromJust . subgoals . varType . dataConWorkId)) . tyConDataCons . thd3) x
      tsDataCons x = map (\x -> if length x == 1 then head x else error " Not singleton ") (tsDataCons' x)
      res0 l = map snd $ filter (\(x, _) -> foldr (\x0 y -> x0 == intTy && y) True x) (zip (tsDataCons l) l)
      res1 l = map snd $ filter (\(x, _) -> foldr (\x0 y -> x0 /= intTy || y) False x) (zip (tsDataCons l) l)
      scruts = x ++ (res0 y1) ++ y3 ++ y4
  modify (\s -> s { scrutinees = scruts })  

synthesizeMatch :: SpecType -> SM [CoreExpr]
synthesizeMatch t = do
  scruts <- scrutinees <$> get
  i <- incrCase 
  case safeIxScruts i scruts of
    Nothing ->  return []
    Just id ->  if null scruts
                  then return []
                  else  let scrut = scruts !! id 
                        in  withIncrDepth (matchOnExpr t (tracepp " [ Current ] " scrut))

synthesizeScrut :: [Var] -> SM [(CoreExpr, Type, TyCon)]
synthesizeScrut vs = do
  exprs <- synthesizeScrutinee vs
  let exprs' = map (\e -> (exprType e, e)) exprs
      isDataCon v = case varType v of { TyConApp c _ -> not . isClassTyCon $ c; _ -> False }
      vs0 = filter isDataCon vs
      es0 = map GHC.Var vs0 
      es1 = map (\e -> (exprType e, e)) es0
      es2 = [(e, t, c) | (t@(TyConApp c _), e) <- es1]
  return (es2 ++ [(e, t, c) | (t@(TyConApp c _), e) <- exprs'])

matchOnExpr :: SpecType -> (CoreExpr, Type, TyCon) -> SM [CoreExpr]
matchOnExpr t (GHC.Var v, tx, c) 
  = matchOn t (v, tx, c)
matchOnExpr t (e, tx, c)
  = do  freshV <- freshVarType tx
        cge <- sCGEnv <$> get 
        freshSpecTy' <- liftCG $ consE cge e
        let freshSpecTy = mapExprReft (const $ mapKVars (\_ -> Just PTrue)) freshSpecTy'
        addEnv freshV freshSpecTy
        es <- matchOn t (freshV, tx, c)
        return $ GHC.Let (GHC.NonRec freshV e) <$> es

matchOn :: SpecType -> (Var, Type, TyCon) -> SM [CoreExpr]
matchOn t (v, tx, c) =
  (GHC.Case (GHC.Var v) v tx <$$> sequence) <$> mapM (makeAlt t (v, tx)) (tyConDataCons c)


makeAlt :: SpecType -> (Var, Type) -> DataCon -> SM [GHC.CoreAlt]
makeAlt t (x, TyConApp _ ts) c = locally $ do
  ts <- liftCG $ mapM trueTy τs
  xs <- mapM freshVar ts    
  newScruts <- synthesizeScrut xs
  modify (\s -> s { scrutinees = scrutinees s ++ newScruts } )
  addsEnv $ zip xs ts 
  addsEmem $ zip xs ts 
  addDecrTerm x xs
  liftCG0 (\γ -> caseEnv γ x mempty (GHC.DataAlt c) xs Nothing)
  es <- synthesizeBasic t
  return $ (GHC.DataAlt c, xs, ) <$> es
  where 
    (_, _, τs) = dataConInstSig c ts
makeAlt _ _ _ = error "makeAlt.bad argument "
