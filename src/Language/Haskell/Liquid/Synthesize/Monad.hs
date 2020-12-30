{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Synthesize.Monad where


import           Language.Haskell.Liquid.Bare.Resolve
                                               as B
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Synthesize.GHC
                                         hiding ( SSEnv )
import           Language.Haskell.Liquid.Synthesize.Misc
                                         hiding ( notrace )
import qualified Language.Fixpoint.Smt.Interface
                                               as SMT
import           Language.Fixpoint.Types hiding ( SEnv
                                                , SVar
                                                , Error
                                                )
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Types.Config
                                               as F
import           CoreSyn                        ( CoreExpr )
import qualified CoreSyn                       as GHC
import           Var
import           Control.Monad.State.Lazy
import qualified Data.HashMap.Strict           as M
import           Data.Maybe
import           Data.List
import           CoreUtils                      ( exprType )
import           Data.Tuple.Extra
import           TyCon
import           TyCoRep
import           Debug.Trace
import           Language.Haskell.Liquid.GHC.TypeRep (showTy)
localMaxMatchDepth :: SM Int 
localMaxMatchDepth = maxMatchDepth . getConfig . sCGEnv <$> get

-------------------------------------------------------------------------------
-- | Synthesis Monad ----------------------------------------------------------
-------------------------------------------------------------------------------

-- The state keeps a unique index for generation of fresh variables 
-- and the environment of variables to types that is expanded on lambda terms
type SSEnv = M.HashMap Symbol (SpecType, Var)
type SSDecrTerm = [(Var, [Var])]

type ExprMemory = [(Type, CoreExpr, Int)]
type T = M.HashMap Type (CoreExpr, Int)
data SState 
  = SState { rEnv       :: !REnv 
           , ssEnv      :: !SSEnv -- Local Binders Generated during Synthesis 
           , ssIdx      :: !Int
           , ssDecrTerm :: !SSDecrTerm 
           , sContext   :: !SMT.Context
           , sCGI       :: !CGInfo
           , sCGEnv     :: !CGEnv
           , sFCfg      :: !F.Config
           , sDepth     :: !Int
           , sExprMem   :: !ExprMemory 
           , sExprId    :: !Int
           , sArgsId    :: !Int
           , sArgsDepth :: !Int
           , sUniVars   :: ![Var]
           , sFix       :: !Var
           , sGoalTys   :: ![Type]
           , sGoalTyVar :: !(Maybe [TyVar])
           , sUGoalTy   :: !(Maybe [Type])     -- Types used for instantiation.
                                               --   Produced by @withUnify@.
           , sLibraries :: !([Var], [[Type]])  -- Polymorphic libraries
           , sCsForalls :: !([Var], [[Type]])  -- Polymorphic constructors
                                               -- [[Type]]: all the types that have instantiated [Var] so far.
           , caseIdx    :: !Int                -- [ Temporary ] Index in list of scrutinees.
           , scrutinees :: ![(CoreExpr, Type, TyCon)]
           }
type SM = StateT SState IO

localMaxAppDepth :: SM Int 
localMaxAppDepth = maxAppDepth . getConfig . sCGEnv <$> get

localMaxArgsDepth :: SM Int
localMaxArgsDepth = maxArgsDepth . getConfig . sCGEnv <$> get

locally :: SM a -> SM a 
locally act = do 
  st <- get 
  r <- act 
  modify $ \s -> s{sCGEnv = sCGEnv st, sCGI = sCGI st, sExprMem = sExprMem st, scrutinees = scrutinees st}
  return r 


evalSM :: SM a -> SMT.Context -> SSEnv -> SState -> IO a 
evalSM act ctx env st = do 
  let st' = st {ssEnv = env}
  r <- evalStateT act st'
  SMT.cleanupContext ctx 
  return r 

initState :: SMT.Context -> F.Config -> CGInfo -> CGEnv -> REnv -> Var -> [Var] -> SSEnv -> IO SState 
initState ctx fcfg cgi cgenv renv xtop uniVars env = 
  return $ SState renv env 0 [] ctx cgi cgenv fcfg 0 exprMem0 0 0 0 uniVars xtop [] Nothing Nothing ([], []) ([], []) 0 []
  where exprMem0 = initExprMem env

getSEnv :: SM SSEnv
getSEnv = ssEnv <$> get 

getSEMem :: SM ExprMemory
getSEMem = sExprMem <$> get

getSFix :: SM Var 
getSFix = sFix <$> get

getSUniVars :: SM [Var]
getSUniVars = sUniVars <$> get

getSDecrTerms :: SM SSDecrTerm 
getSDecrTerms = ssDecrTerm <$> get

addsEnv :: [(Var, SpecType)] -> SM () 
addsEnv xts = 
  mapM_ (\(x,t) -> modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)})) xts  

addsEmem :: [(Var, SpecType)] -> SM () 
addsEmem xts = do 
  curAppDepth <- sExprId <$> get
  mapM_ (\(x,t) -> modify (\s -> s {sExprMem = (toType t, GHC.Var x, curAppDepth+1) : (sExprMem s)})) xts  
  

addEnv :: Var -> SpecType -> SM ()
addEnv x t = do 
  liftCG0 (\γ -> γ += ("arg", symbol x, t))
  modify (\s -> s {ssEnv = M.insert (symbol x) (t,x) (ssEnv s)}) 

addEmem :: Var -> SpecType -> SM ()
addEmem x t = do 
  let ht0 = toType t
  curAppDepth <- sExprId <$> get
  xtop <- getSFix 
  (ht1, _) <- instantiateTL
  let ht = if x == xtop then ht1 else ht0
  modify (\s -> s {sExprMem = (ht, GHC.Var x, curAppDepth) : sExprMem s})

---------------------------------------------------------------------------------------------
--                         Handle structural termination checking                          --
---------------------------------------------------------------------------------------------
addDecrTerm :: Var -> [Var] -> SM ()
addDecrTerm x vars = do
  decrTerms <- getSDecrTerms 
  case lookup x decrTerms of 
    Nothing    -> lookupAll x vars decrTerms
    Just vars' -> do
      let ix = elemIndex (x, vars') decrTerms
          newDecrs = thisReplace (fromMaybe (error " [ addDecrTerm ] Index ") ix) (x, vars ++ vars') decrTerms
      modify (\s -> s { ssDecrTerm =  newDecrs })

-- 
lookupAll :: Var -> [Var] -> SSDecrTerm -> SM ()
lookupAll x vars []               = modify (\s -> s {ssDecrTerm = (x, vars) : ssDecrTerm s})
lookupAll x vars ((xl, vs):decrs) =
  case find (== x) vs of
    Nothing -> lookupAll x vars decrs
    Just _  -> do
      sDecrs <- ssDecrTerm <$> get
      let newDecr  = (xl, vars ++ [x] ++ vs)
          i        = fromMaybe (error " Write sth ") (elemIndex (xl, vs) sDecrs)
          newDecrs = thisReplace i newDecr decrs
      modify (\s -> s { ssDecrTerm = newDecrs })

thisReplace :: Int -> a -> [a] -> [a]
thisReplace i x l
  = left ++ [x] ++ right
    where left  = take (i-1) l
          right = drop i l

-- | Entry point.
structuralCheck :: [CoreExpr] -> SM [CoreExpr]
structuralCheck es 
  = do  decr <- ssDecrTerm <$> get
        fix <- sFix <$> get
        return (filter (notStructural decr fix) es)

structCheck :: Var -> CoreExpr -> (Maybe Var, [CoreExpr])
structCheck xtop var@(GHC.Var v)
  = if v == xtop 
      then (Just xtop, [])
      else (Nothing, [var])
structCheck xtop (GHC.App e1 (GHC.Type _))
  = structCheck xtop e1
structCheck xtop (GHC.App e1 e2)
  =  (mbVar, e2:es)
    where (mbVar, es) = structCheck xtop e1
structCheck xtop (GHC.Let _ e) 
  = structCheck xtop e
structCheck _ e 
  = error (" StructCheck " ++ show e)

notStructural :: SSDecrTerm -> Var -> CoreExpr -> Bool
notStructural decr xtop e
  = case v of
      Nothing -> True
      Just _  -> foldr (\x b -> isDecreasing' x decr || b) False args
  where (v, args) = structCheck xtop e

isDecreasing' :: CoreExpr -> SSDecrTerm -> Bool
isDecreasing' (GHC.Var v) decr
  = v `notElem` map fst decr
isDecreasing' _e _decr
  = True
---------------------------------------------------------------------------------------------
--                               END OF STRUCTURAL CHECK                                   --
---------------------------------------------------------------------------------------------

liftCG0 :: (CGEnv -> CG CGEnv) -> SM () 
liftCG0 act = do 
  st <- get 
  let (cgenv, cgi) = runState (act (sCGEnv st)) (sCGI st) 
  modify (\s -> s {sCGI = cgi, sCGEnv = cgenv}) 


liftCG :: CG a -> SM a 
liftCG act = do 
  st <- get 
  let (x, cgi) = runState act (sCGI st) 
  modify (\s -> s {sCGI = cgi})
  return x 


freshVarType :: Type -> SM Var
freshVarType t = (\i -> mkVar (Just "x") i t) <$> incrSM


freshVar :: SpecType -> SM Var
freshVar = freshVarType . toType

withIncrDepth :: Monoid a => SM a -> SM a
withIncrDepth m = do 
    s <- get
    matchBound <- localMaxMatchDepth 
    let d = sDepth s
    if d + 1 > matchBound
      then return mempty
      else do put s{sDepth = d + 1}
              r <- m
              modify $ \s -> s{sDepth = d}
              return r
        
  
incrSM :: SM Int 
incrSM = do s <- get 
            put s{ssIdx = ssIdx s + 1}
            return (ssIdx s)

incrCase :: SM Int 
incrCase
  = do  s <- get 
        put s { caseIdx = caseIdx s + 1 }
        return (caseIdx s)
  
safeIxScruts :: Int -> [a] -> Maybe Int
safeIxScruts i l 
  | i >= length l = Nothing
  | otherwise     = Just i

symbolExpr :: Type -> F.Symbol -> SM CoreExpr 
symbolExpr τ x = incrSM >>= (\i -> return $ F.notracepp ("symExpr for " ++ F.showpp x) $  GHC.Var $ mkVar (Just $ F.symbolString x) i τ)


-------------------------------------------------------------------------------------------------------
----------------------------------------- Handle ExprMemory -------------------------------------------
-------------------------------------------------------------------------------------------------------

-- | Initializes @ExprMemory@ structure.
--    1. Transforms refinement types to conventional (Haskell) types.
--    2. All @Depth@s are initialized to 0.
initExprMem :: SSEnv -> ExprMemory
initExprMem sEnv = map (\(_, (t, v)) -> (toType t, GHC.Var v, 0)) (M.toList sEnv)


-------------- Init @ExprMemory@ with instantiated functions with the right type (sUGoalTy) -----------
insEMem0 :: SSEnv -> SM ExprMemory
insEMem0 senv = do
  xtop      <- getSFix
  (ttop, _) <- instantiateTL
  mbUTy     <- sUGoalTy <$> get 
  uniVs <- sUniVars <$> get

  let ts = fromMaybe [] mbUTy
  ts0 <- snd . sCsForalls <$> get
  fs0 <- fst . sCsForalls <$> get
  modify ( \s -> s { sCsForalls = (fs0, ts : ts0) } )

  let handleIt e = case e of  GHC.Var v -> if xtop == v 
                                              then (instantiate e (Just uniVs), ttop) 
                                              else change e
                              _         -> change e
      change e =  let { e' = instantiateTy e mbUTy; t' = exprType e' } 
                  in  (e', t')

      em0 = initExprMem senv
  return $ map (\(_, e, i) -> let (e', t') = handleIt e
                              in  (t', e', i)) em0

instantiateTy :: CoreExpr -> Maybe [Type] -> CoreExpr
instantiateTy e mbTy = 
  case mbTy of 
    Nothing  -> e
    Just tys -> case applyTy tys e of 
                  Nothing -> e
                  Just e0 -> e0

-- | Used for instantiation: Applies types to an expression.
--   > The result does not have @forall@.
--   Nothing as a result suggests that there are more types than foralls in the expression.
applyTy :: [Type] -> GHC.CoreExpr -> Maybe GHC.CoreExpr
applyTy []     e =  case exprType e of 
                      ForAllTy{} -> Nothing
                      _          -> Just e
applyTy (t:ts) e =  case exprType e of
                      ForAllTy{} -> applyTy ts (GHC.App e (GHC.Type t))
                      _          -> Nothing

-- | Instantiation based on current goal-type.
fixEMem :: SpecType -> SM ()
fixEMem t
  = do  (fs, ts) <- sCsForalls <$> get
        (libs, lts) <- sLibraries <$> get
        let uTys = unifyWith (toType t)
        needsFix <- case find (== uTys) ts of 
                      Nothing -> return True   -- not yet instantiated
                      Just _  -> return False  -- already instantiated

        let libTs = fixLibs libs t 
        goalTyVar' <- sUGoalTy <$> get
        uniVs <- sUniVars <$> get
        let goalTyVar = fromMaybe [] goalTyVar'

        let uLibTys = map TyVarTy uniVs -- TODO Construct types 

        libsNeedFix <-  case find (== uLibTys) ts of
                          Nothing -> return True 
                          Just _  -> return False 

        trace (" [ fixEMem ] GoalType " ++ show t ++ " Libraries " ++ show libs ++ 
               " Types of libraries " ++ show (map (showTy . exprType . GHC.Var) libs) ++
               " ***NEW*** Types of libraries " ++ show (map showTy libTs) ++
               " Searching type variables " ++ show (map showTy uTys) ++ 
               " Goal type variable " ++ show (map showTy goalTyVar) ++ 
               " Synthesis unification variables " ++ show uniVs ++ 
               " Ordered variables " ++ show (map (getVarsOrdered . exprType . GHC.Var) libs)) $
          when needsFix $
            do  modify (\s -> s { sCsForalls = (fs, uTys : ts)})
                let notForall e = case exprType e of {ForAllTy{} -> False; _ -> True}
                    es = map (\v -> instantiateTy (GHC.Var v) (Just uTys)) fs
                    fixEs = filter notForall es
                thisDepth <- sDepth <$> get
                let fixedEMem = map (\e -> (exprType e, e, thisDepth + 1)) fixEs
                modify (\s -> s {sExprMem = fixedEMem ++ sExprMem s})

        when libsNeedFix $
          do modify (\s -> s {sLibraries = (libs, uLibTys : lts)})
             let tyCands t0 = [(x, y) | x <- freeTyVars' t0, y <- uLibTys]
                 libTyCands = map tyCands libTs -- [[(Var, Type)]]
                 boundVars = map (map fst) uResVars
                 orderedTyVars = map (getVarsOrdered . exprType . GHC.Var) libs
                 freeTyVars = getFreeTyVars orderedTyVars boundVars
                 uResVars = unified libs t 
                 searched = map (map (\(x, y) -> (x, TyVarTy y))) searched'
                 searched' = searchTyVars uniVs freeTyVars
                 vsToTs = combineTyVars uResVars searched
                 testFn ls = groupBy (\x y -> fst x == fst y) ls -- [[[(Var, Type)]]]
                 test = map testFn libTyCands
                 vs3 = map (map head) (map (map (map fst)) test) 
                 ts3 = map (map (map snd)) test
                 orderedBinds = maintain orderedTyVars vsToTs
                 orderedTs = map (map snd) orderedBinds
                 instantiated = instantiateLibs libs orderedTs
                 notForall e = case exprType e of {ForAllTy{} -> False; _ -> True}
                 fixedLibs = filter notForall instantiated 
             curDepth <- sDepth <$> get
             let emem1 = map (\e -> (exprType e, e, curDepth + 1)) fixedLibs

             trace (" Bound Variables " ++ show boundVars ++ 
                    " Free Vars " ++ show freeTyVars ++ 
                    " searched " ++ show (map (map fst) orderedBinds) ++
                    " instantiated " ++ show instantiated) $
              modify (\s -> s {sExprMem = emem1 ++ sExprMem s})

instantiateLibs :: [Var] -> [[Type]] -> [CoreExpr]
instantiateLibs [] []
  = []
instantiateLibs (v:vs) (ts0:ts)
  = instantiateTy (GHC.Var v) (Just ts0) : instantiateLibs vs ts
instantiateLibs _ _ 
  = error " instantiateLibs "

-- First: type variables as they appear at the initial library function type
-- Second: bindings from type variables to types as they were created by the unification and search
-- Order second argument with respect to the first 
maintain :: [[Var]] -> [[(Var, Type)]] -> [[(Var, Type)]]
maintain [] [] 
  = []
maintain (vs0:vs) (tvs0:tvs) 
  = maintain' vs0 tvs0 : maintain vs tvs
maintain _ _ 
  = error " maintain "

maintain' :: [Var] -> [(Var, Type)] -> [(Var, Type)]
maintain' []     _
  = []
maintain' (v:vs) tvs
  = case lookup v tvs of 
      Nothing -> error $ " Should contain type variable " ++ show v
      Just t  -> (v, t) : maintain' vs tvs

-- First argument: type variables used in current top level function 
searchTyVars :: [Var] -> [[Var]] -> [[(Var, Var)]]
searchTyVars _  []
  = []
searchTyVars vs (f:fs) 
  = [(x, y) | x <- f, y <- vs] : searchTyVars vs fs

combineTyVars :: [[(Var, Type)]] -> [[(Var, Type)]] -> [[(Var, Type)]]
combineTyVars [] [] 
  = []
combineTyVars (tvs0:tvs) (tvs1:tvs') 
  = (tvs0 ++ tvs1) : combineTyVars tvs tvs'
combineTyVars tvs tvs' 
  = error $ " [ combineTyVars ] tvs " ++ show (map (map fst) tvs) ++ " tvs' " ++ show (map (map fst) tvs')

getFreeTyVars :: [[Var]] -> [[Var]] -> [[Var]]
getFreeTyVars [] [] = []
getFreeTyVars (tv:tvs) (btv:btvs) 
  = (tv \\ btv) : getFreeTyVars tvs btvs
getFreeTyVars v0 v1 = error (" [ getFreeTyVars ] v0 " ++ show v0 ++ " v1 " ++ show v1)

getVarsOrdered :: Type -> [Var]
getVarsOrdered (ForAllTy (Bndr v _) t) 
  = v : getVarsOrdered t
getVarsOrdered t 
  = []

reorderVars :: [[[(Var, Type)]]] -> [(Var, Type)]
reorderVars [ ] = []
reorderVars (tvs:tvss) = 
  let vs = map (map fst) tvs -- type variables (should equal to one variable)
      ts = map (map snd) tvs -- types associated with variables
  in  trace (" [ reorderVars ] VS " ++ show vs) $
        reorderVars tvss -- (head vs, concat ts) : reorderVars tvss

-- Perform type application to the term rather than substitution to the type 
-- Maintain ordering for type application 

-- Get @libTs@ and find free type variables 
freeTyVars' :: Type -> [Var]
freeTyVars' (ForAllTy (Bndr v _) t) 
  = v : freeTyVars' t 
freeTyVars' t 
  = [] 


-- TODO Construct types for type application 

unified :: [Var] -> SpecType -> [[(Var, Type)]]
unified libs t =
  let libU x = unify (resTy (exprType (GHC.Var x))) (resTy (toType t)) 
  in  map libU libs 

fixLibs :: [Var] -> SpecType -> [Type]
fixLibs libs t = 
  let res x   = unify (resTy (exprType (GHC.Var x))) (resTy (toType t)) 
      allRes  = map res libs -- [[(Var, Type)]]
      libTs   = map (exprType . GHC.Var) libs
      comb    = zip libTs allRes
      libTs'  = map (uncurry rmForAllVars) comb
      comb'   = zip libTs' allRes
      libTs'' = map (uncurry subToTypes) comb'
  in libTs''


-- Get result type of library (library has a function type)
resTy :: Type -> Type
resTy (ForAllTy _ t) = resTy t
resTy (FunTy _ _ t)  = resTy t 
resTy t              = t

-- Unify result goal type with library result type 
--  First argument is the result type of the polymorphic library function 
--  Second argument is the type of the synthesis goal
unify :: Type -> Type -> [(Var, Type)]
unify (TyVarTy v) t@(TyConApp c ts) 
  = [(v, t)] 
unify (TyConApp c0 ts0) (TyConApp c1 ts1) 
  = let vs0  = getVar ts0 
    in  zip vs0 ts1
unify t0 t1 
  = trace (" unify wildcard t0 " ++ showTy t0 ++ " t1 " ++ showTy t1) []

getVar :: [Type] -> [Var] 
getVar [ ] 
  = [ ]
getVar (TyVarTy v : ts) 
  = v : getVar ts
getVar ts 
  = trace (" [ getVar ] Not type variable case " ++ show (map showTy ts)) [] 

rmForAllVars :: Type -> [(Var, Type)] -> Type
rmForAllVars t [] 
  = t
rmForAllVars (ForAllTy (Bndr v a) t) vts
  = case lookup v vts of 
      Nothing -> ForAllTy (Bndr v a) (rmForAllVars t vts)
      Just _  -> rmForAllVars t vts
rmForAllVars t vts
  = trace (" Got more type variables " ++ showTy t ++ " vs " ++ show (map fst vts) ) t

-- Substitute to library's type
subToType :: Type -> (Var, Type) -> Type
subToType t0@(TyVarTy v0) (v, t) = if v0 == v then t else t0
subToType (AppTy t0 t1) (v, t) = AppTy (subToType t0 (v, t)) (subToType t1 (v, t))
subToType (TyConApp c ts) (v, t) = TyConApp c (map (\x -> subToType x (v, t)) ts)
subToType (ForAllTy v0 t0) (v, t) = ForAllTy v0 (subToType t0 (v, t))
subToType (FunTy a t0 t1) (v, t) = FunTy a (subToType t0 (v, t)) (subToType t1 (v, t))
subToType t _ = t

subToTypes :: Type -> [(Var, Type)] -> Type
subToTypes t [] = t
subToTypes t0 ((v, t):vts) = 
  let t' = subToType t0 (v, t)
  in  subToTypes t' vts

------------------------------------------------------------------------------------------------
------------------------------ Special handle for the current fixpoint -------------------------
------------------------------------------------------------------------------------------------

-- | Instantiate the top-level variable.
instantiateTL :: SM (Type, GHC.CoreExpr)
instantiateTL = do
  uniVars <- getSUniVars 
  xtop <- getSFix
  let e = fromJust $ apply uniVars (GHC.Var xtop)
  return (exprType e, e)

-- | Applies type variables (1st argument) to an expression.
--   The expression is guaranteed to have the same level of 
--   parametricity (same number of @forall@) as the length of the 1st argument.
--   > The result has zero @forall@.
apply :: [Var] -> GHC.CoreExpr -> Maybe GHC.CoreExpr
apply []     e = 
  case exprType e of 
    ForAllTy {} -> Nothing
    _           -> Just e
apply (v:vs) e 
  = case exprType e of 
      ForAllTy{} -> apply vs (GHC.App e (GHC.Type (TyVarTy v)))
      _          -> Nothing

instantiate :: CoreExpr -> Maybe [Var] -> CoreExpr
instantiate e mbt = 
  case mbt of
    Nothing     -> e
    Just tyVars -> case apply tyVars e of 
                      Nothing -> e
                      Just e' -> e'

-----------------------------------------------------------------------------------------------------

withTypeEs :: SpecType -> SM [CoreExpr] 
withTypeEs t = do 
    em <- sExprMem <$> get 
    return (map snd3 (filter (\x -> fst3 x == toType t) em)) 

findCandidates :: Type ->         -- Goal type: Find all candidate expressions of this type,
                                  --   or that produce this type (i.e. functions).
                  SM ExprMemory
findCandidates goalTy = do
  sEMem <- sExprMem <$> get
  return (filter ((goalType goalTy) . fst3) sEMem)

functionCands :: Type -> SM [(Type, GHC.CoreExpr, Int)]
functionCands goalTy = do 
  all <- findCandidates goalTy 
  return (filter (isFunction . fst3) all)


---------------------------------------------------------------------------------
--------------------------- Generate error expression ---------------------------
---------------------------------------------------------------------------------

varError :: SM Var
varError = do 
  info    <- ghcI . sCGI <$> get
  let env  = B.makeEnv (gsConfig $ giSpec info) (toGhcSrc $ giSrc info) mempty mempty 
  let name = giTargetMod $ giSrc info
  return $ B.lookupGhcVar env name "Var" (dummyLoc $ symbol "Language.Haskell.Liquid.Synthesize.Error.err")

toGhcSrc :: TargetSrc -> GhcSrc 
toGhcSrc a = Src
      { _giIncDir    = giIncDir a
      , _giTarget    = giTarget a
      , _giTargetMod = giTargetMod a
      , _giCbs       = giCbs a
      , _gsTcs       = gsTcs a
      , _gsCls       = gsCls a
      , _giDerVars   = giDerVars a
      , _giImpVars   = giImpVars a
      , _giDefVars   = giDefVars a
      , _giUseVars   = giUseVars a
      , _gsExports   = gsExports a
      , _gsFiTcs     = gsFiTcs a
      , _gsFiDcs     = gsFiDcs a
      , _gsPrimTcs   = gsPrimTcs a
      , _gsQualImps  = gsQualImps a
      , _gsAllImps   = gsAllImps a
      , _gsTyThings  = gsTyThings a
      }