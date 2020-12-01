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
import           CoreUtils (exprType)
import           TyCoRep
import           Language.Haskell.Liquid.GHC.Play
import           Debug.Trace 
import           Language.Fixpoint.Types.Visitor (mapKVars)
import           Language.Haskell.Liquid.GHC.TypeRep (showTy)
synthesize :: FilePath -> F.Config -> CGInfo -> IO [Error]
synthesize tgt fcfg cginfo = 
  mapM go (M.toList $ holesMap cginfo)
  where 
    measures = map (val . msName) ((gsMeasures . gsData . giSpec . ghcI) cginfo)
    go (x, HoleInfo rType loc env (cgi,cge)) = do 
      let topLvlBndr = fromMaybe (error "Top-level binder not found") (cgVar cge)
          typeOfTopLvlBnd = fromMaybe (error "Type: Top-level symbol not found") (M.lookup (symbol topLvlBndr) (reGlobal env))
          coreProgram = giCbs $ giSrc $ ghcI cgi
          (uniVars, _) = getUniVars coreProgram topLvlBndr
          fromREnv' = filterREnv (reLocal env)
          fromREnv'' = M.fromList (filter (rmClassVars . toType . snd) (M.toList fromREnv'))
          rmClassVars t = case t of { TyConApp c _ -> not . isClassTyCon $ c; _ -> True }
          fromREnv  = M.fromList (rmMeasures measures (M.toList fromREnv''))
          isForall t = case t of { ForAllTy{} -> True; _ -> False}
          rEnvForalls = M.fromList (filter (isForall . toType . snd) (M.toList fromREnv))
          fs = map (snd . snd) $ M.toList (symbolToVar coreProgram topLvlBndr rEnvForalls)

          ssenv0' = symbolToVar coreProgram topLvlBndr fromREnv
          ssenv0 = filter (\(_, (_, v)) -> not (isHoleVar v)) (M.toList ssenv0')
          (senv1, foralls') = initSSEnv typeOfTopLvlBnd cginfo (M.fromList ssenv0)
      
      ctx <- SMT.makeContext fcfg tgt
      state0 <- initState ctx fcfg cgi cge env topLvlBndr (reverse uniVars) M.empty
      let foralls = foralls' ++ fs
          todo = if findDef coreProgram topLvlBndr then typeOfTopLvlBnd else rType
      fills <- synthesize' ctx cgi senv1 todo topLvlBndr typeOfTopLvlBnd foralls state0

      notrace (" SYNTHESIS TODO Type: " ++ show todo ++ " RType " ++ show rType) $
        return $ ErrHole loc (
          if not (null fills)
            then text "\n Hole Fills:" $+$ pprintMany (map (coreToHs typeOfTopLvlBnd topLvlBndr . fromAnf) fills)
            else mempty) mempty (symbol x) typeOfTopLvlBnd 

findDef :: GHC.CoreProgram -> Var -> Bool 
findDef []     _ = False
findDef (x:xs) v = 
  case x of 
    bnd@(GHC.NonRec b e) ->  
      let (f, e1) = topHole e 
      in  if v == b 
            then notrace (" FIND DEF Expr = " ++ showpp bnd) $ (f && holeForm e1) || findDef xs v
            else findDef xs v 
    _ -> findDef xs v

holeForm :: GHC.CoreExpr -> Bool
holeForm (GHC.Tick _ (GHC.Tick _ (GHC.Var v))) = isHoleVar v
holeForm _ = False 

countLams :: GHC.CoreExpr -> Int -> (Int, CoreExpr)
countLams (GHC.Lam _ e) i 
  = countLams e (i+1)
countLams e i = (i, e)

countApps :: GHC.CoreExpr -> Int -> (Bool, GHC.CoreExpr)
countApps (GHC.App e1 e2) i = 
  countApps e1 (i-1)
countApps e i 
  | i == 0    = (True, e)
  | otherwise = (False, e)

unLam :: Int -> GHC.CoreExpr -> (Bool, GHC.CoreExpr)
unLam i (GHC.Lam _ e) = unLam (i-1) e
unLam i e | i == 0    = (True, e)
          | otherwise = (False, e)

topHole :: CoreExpr -> (Bool, CoreExpr)
topHole e0 = 
  let (i, e1) = countLams e0 0 
      (b, e2) = countApps e1 i 
  in  if b  then  case e2 of 
                    (GHC.Let _ (GHC.Let _ e3)) -> 
                      let (flag, e4) = unLam i e3
                      in  (flag, e4)
                    _ -> (False, e2)
            else  (False, e2)

synthesize' :: SMT.Context -> CGInfo -> SSEnv -> SpecType ->  Var -> SpecType -> [Var] -> SState -> IO [CoreExpr]
synthesize' ctx cgi senv tx xtop ttop foralls st2
 = evalSM (go tx) ctx senv st2
  where 

    go :: SpecType -> SM [CoreExpr]

    -- Type Abstraction 
    go (RAllT a t _x)      = GHC.Lam (tyVarVar a) <$$> go t
          
    go t@(RApp c _ts _ _r) = do  
      let coreProgram = giCbs $ giSrc $ ghcI cgi
          args  = filter (not . isTyVar) (drop 1 (argsP coreProgram xtop))
          (_, (xs, txs, _), _) = bkArrow ttop
          dt = decrType xtop ttop args (zip xs txs)
      addEnv xtop dt
      addEmem xtop dt  
      senv1 <- getSEnv 

      if R.isNumeric (tyConEmbed cgi) c
          then error " [ Numeric in synthesize ] Update liquid fixpoint. "
          else do let ts = unifyWith (toType t)
                  if null ts  then modify (\s -> s { sUGoalTy = Nothing } )
                              else modify (\s -> s { sUGoalTy = Just ts } )
                  modify (\s -> s {sForalls = (foralls, [])})
                  emem0 <- insEMem0 senv1
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
              mapM_ (`addDecrTerm` []) ys
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
  es <- genTerms t
  if null es  then synthesizeMatch t
              else return es

synthesizeMatch :: SpecType -> SM [CoreExpr]
synthesizeMatch t = do
  scruts <- scrutinees <$> get
  i <- incrCase 
  case safeIxScruts i scruts of
    Nothing ->  return []
    Just id ->  if null scruts
                  then return []
                  else withIncrDepth (matchOnExpr t (scruts !! id))

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
        freshSpecTy' <- liftCG $ trueTy tx
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
