{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Haskell.Liquid.Synthesize.Generate where

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Synthesize.GHC
                                         hiding ( SSEnv )
import           Language.Haskell.Liquid.Synthesize.Monad
import           Language.Haskell.Liquid.Synthesize.Misc
                                         hiding ( notrace )
import           Language.Haskell.Liquid.Synthesize.Check
import           CoreSyn                        ( CoreExpr )
import qualified CoreSyn                       as GHC
import           Data.Maybe
import           Control.Monad.State.Lazy
import           Language.Haskell.Liquid.Constraint.Fresh
                                                ( trueTy )
import           Data.List
import           CoreUtils (exprType)
import           Var
import           Data.Tuple.Extra
-- import           Language.Fixpoint.Types.PrettyPrint (tracepp)
import           TyCoRep
-- import           Language.Haskell.Liquid.GHC.TypeRep (showTy)
-- import           Language.Fixpoint.Types.Refinements
import           Debug.Trace
import           Language.Haskell.Liquid.GHC.TypeRep (showTy)

-- Generate terms that have type t: This changes the @ExprMemory@ in @SM@ state.
-- Return expressions type checked against type @specTy@.
genTerms :: SpecType -> SM [CoreExpr] 
genTerms = genTerms' ResultMode


data SearchMode 
  = ArgsMode          -- ^ searching for arguments of functions that can eventually 
                      --   produce the top level hole fill
  | ResultMode        -- ^ searching for the hole fill 
  deriving (Eq, Show) 

-- hasHType :: SpecType -> CoreExpr -> SM Bool
-- hasHType t e = 
--   if checkTrueType t then return (toType t == exprType e)
--                      else hasType t e

genTerms' :: SearchMode -> SpecType -> SM [CoreExpr] 
genTerms' i specTy = 
  do  goalTys <- sGoalTys <$> get
      case find (== toType specTy) goalTys of 
        Nothing -> modify (\s -> s { sGoalTys = toType specTy : sGoalTys s })
        Just _  -> return ()
      fixEMem specTy 
      fnTys <- functionCands (toType specTy)
      es    <- withTypeEs specTy 
      es0   <- structuralCheck es

      err <- checkError specTy
      trace (" [ genTerms' ] t = " ++ show specTy ++ " Function candidates " ++ show (map snd3 fnTys)) $ 
        case err of 
          Nothing -> filterElseM (hasType specTy) es0 $ withDepthFill i specTy 0 fnTys
          Just e -> return [e]

genArgs :: SpecType -> SM [CoreExpr]
genArgs t =
  do  goalTys <- sGoalTys <$> get
      case find (== toType t) goalTys of 
        Nothing -> do modify (\s -> s { sGoalTys = toType t : sGoalTys s }) 
                      fixEMem t 
                      fnTys <- functionCands (toType t)
                      es <- withDepthFillArgs t 0 fnTys
                      trace (" [ genArgs ] t = " ++ show t ++ show (map snd3 fnTys)) $
                        if null es
                          then  return []
                          else  do  -- modify (\s -> s {sExprId = sExprId s + 1})
                                    return es
        Just _  -> return []

withDepthFillArgs :: SpecType -> Int -> [(Type, CoreExpr, Int)] -> SM [CoreExpr]
withDepthFillArgs t depth cs = do
  thisEm <- sExprMem <$> get
  es <- argsFill thisEm cs []
  argsDepth <- localMaxArgsDepth

  filterElseM (hasType t) es $
    if depth < argsDepth
      then  -- trace (" [ withDepthFillArgs ] argsDepth = " ++ show argsDepth) $ 
            withDepthFillArgs t (depth + 1) cs
      else  return []

argsFill :: ExprMemory -> [(Type, CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr]
argsFill _   []               es0 = return es0 
argsFill em0 (c:cs) es0 =
  case subgoals (fst3 c) of
    Nothing             -> return [] 
    Just (resTy, subGs) -> 
      do  let argCands = map (withSubgoal em0) subGs
              toGen    = foldr (\x b -> (not . null) x && b) True argCands
              fnArgs   = hasFunArg c 
              hasFnArg = checkFnArgs fnArgs
          es <- do  curExprId <- sExprId <$> get
                    trace (" [ argsFill ] c = " ++ show (snd3 c) ++ 
                           " toGen flag " ++ show toGen ++ 
                           " Candidate arguments " ++ show argCands ++ 
                           " HAVE FUNCTIONS " ++ show (map (\(x, y) -> (showTy x, y)) (hasFunArg c)) ++ 
                           " Library's name " ++ show (getName (snd3 c))) $
                      if toGen 
                        then prune curExprId c argCands
                        else 
                          if hasFnArg 
                            then do 
                              no <- noVars (getName (snd3 c))
                              fns <- generateFns no fnArgs
                              let argCands' = repairArgs curExprId fns argCands
                                  checkRepair = repaired argCands'
                              if checkRepair 
                                then prune curExprId c argCands'
                                else return []
                            else return []
          curExprId <- sExprId <$> get
          let nextEm = map (resTy, , curExprId + 1) es
          modify (\s -> s {sExprMem = nextEm ++ sExprMem s })
          argsFill em0 cs (es ++ es0)

getName :: CoreExpr -> Var 
getName (GHC.Var v) 
  = v
getName (GHC.App e1 _)
  = getName e1
getName e 
  = error (" [ getName ] Expression " ++ show e)

-- TODO Produce new functions only if the other arguments have candidate expressions 

repaired :: [[(CoreExpr, Int)]] -> Bool 
repaired = foldr (\x b -> (not . null) x && b) True 

repairArgs :: Int -> [(Type, Maybe Int, [CoreExpr])] -> [[(CoreExpr, Int)]] -> [[(CoreExpr, Int)]]
repairArgs _ [] es
  = es
repairArgs curId ((_, mb, es0):ts) es
  = case mb of 
      Nothing -> repairArgs curId ts es
      Just ix -> 
        let depthEs = map (, curId) es0
            es'     = changeIx ix depthEs es
        in  repairArgs curId ts es'

-- First argument is 1-based index.
changeIx :: Int -> [(CoreExpr, Int)] -> [[(CoreExpr, Int)]] -> [[(CoreExpr, Int)]]
changeIx = changeIx' 1

changeIx' :: Int -> Int -> [(CoreExpr, Int)] -> [[(CoreExpr, Int)]] -> [[(CoreExpr, Int)]]
changeIx' _  i _  []
  = error $ " [ changeIx' ] Index based search: index not found " ++ show i 
changeIx' i0 i es0 (e:es) 
  | i0 == i   = es0:es
  | otherwise = e : changeIx' (i0+1) i es0 es

-- This should be a function type 
-- Filter expressions used to synthesize the function
generateFn :: [Var] -> Type -> SM [CoreExpr]
generateFn vs t
  = do  let txs = getFnArg t
            out = getOutArg t
        specTxs <- liftCG $ mapM trueTy txs
        specOut <- liftCG $ trueTy out 
        ys <- mapM freshVar specTxs
        locals <- localFns <$> get
        case lookup4 t locals of 
          Nothing -> 
            do  localEM <- consLocalEM vs ys
                modify (\s -> s {localFns = (t, localEM, [], False) : localFns s})
                GHC.mkLams ys <$$> synthesizeFun t specOut
          Just (_, es, _) -> 
            return es

lookup4 :: Eq a => a -> [(a, b, c, d)] -> Maybe (b, c, d)
lookup4 _ []
  = Nothing
lookup4 k ((k0, v1, v2, v3):xs)
  | k0 == k   = Just (v1, v2, v3)
  | otherwise = lookup4 k xs

-- TODO Remove current top level function, current library's name, constructors.
noVars :: Var -> SM [Var]
noVars v = 
  do  st <- get 
      let ctl = sFix st 
          cs = sCsForalls st 
      return (v : ctl : fst cs)


localFilter :: [Var] -> CoreExpr -> Bool
localFilter no (GHC.Var v) 
  = not (exists v no)
localFilter _ e 
  = trace (" [ localFilter ] Expression " ++ show e) False

localFilterEM :: [Var] -> [(Type, CoreExpr, Int)] -> [(Type, CoreExpr, Int)]
localFilterEM no = filter (\(_, e, _) -> localFilter no e)

exists :: Eq a => a -> [a] -> Bool
exists _ []     = False
exists k (x:xs) = x == k || exists k xs

localExprMem :: [Var] -> SM [(Type, CoreExpr, Int)] 
localExprMem no = do 
  localEM <- forLocal <$> get
  if null localEM 
    then do em <- sExprMem <$> get 
            modify (\s -> s {forLocal = em})
            return (localFilterEM no em) 
    else return localEM

withLocals :: Int -> [(Type, CoreExpr, Int)] -> [Var] -> [(Type, CoreExpr, Int)]
withLocals curId em vs = 
  let es  = map GHC.Var vs
      ts  = map exprType es
      ids = replicate (length es) curId
  in  zip3 ts es ids ++ em

consLocalEM :: [Var] -> [Var] -> SM [(Type, CoreExpr, Int)]
consLocalEM no vs = do 
  filtered <- localExprMem no
  curExprId <- sExprId <$> get
  return (withLocals curExprId filtered vs)

-- When the program gets here, @localFns@ are initiated but 
-- production flag is off. Production flag is used in order to 
-- separate empty synthesis result from no synthesis.
synthesizeFun :: Type -> SpecType -> SM [CoreExpr]
synthesizeFun t0 t 
  = do  lcs <- localFns <$> get
        case lookup4 t0 lcs of 
          Nothing          -> error (" [ synthesizeFun ] Type " ++ show t0)
          Just (em, es, b) -> 
            if b 
              then return es
              else trace (" [ synthesizeFun ] Expressions to be used " ++ show (map snd3 em)) (withEMProduce em)

withEMProduce :: ExprMemory -> [CoreExpr]
withEMProduce em = undefined

generateFns :: [Var] -> [(Type, Maybe Int)] -> SM [(Type, Maybe Int, [CoreExpr])]
generateFns _ [] 
  = return []
generateFns vs ((t, mbIx):ts) 
  = do  es0 <- case mbIx of {Nothing -> return []; Just _ -> generateFn vs t}  
        es  <- generateFns vs ts
        return ((t, mbIx, es0):es)

checkFnArgs :: [(Type, Maybe Int)] -> Bool
checkFnArgs [] 
  = False
checkFnArgs ((_, Just _):_) 
  = True 
checkFnArgs ((_, Nothing):ts) 
  = checkFnArgs ts

-- Input is always a function.
hasFunArg :: (Type, CoreExpr, Int) -> [(Type, Maybe Int)]
hasFunArg (t, _, _) 
  = let ts  = getFnArg t 
        fns = map isFn ts 
        is  = ixs 1 fns
    in  zip ts is

isFn :: Type -> Bool 
isFn FunTy{} = True 
isFn _       = False

getFnArg :: Type -> [Type]
getFnArg (FunTy _ t1 t2) 
  = t1 : getFnArg t2
-- Inserts here when we have the output type
getFnArg _
  = []

ixs :: Int -> [Bool] -> [Maybe Int]
ixs _ []
  = []
ixs i (b:bs) 
  = if b 
      then Just i : ixs (i+1) bs
      else Nothing : ixs (i+1) bs

-- Input is a function type
getOutArg :: Type -> Type 
getOutArg (FunTy _ _ t2) 
  = getOutArg t2
getOutArg t 
  = t

-- checkTrueType :: SpecType -> Bool 
-- checkTrueType (RApp _ _ _ (MkUReft (Reft (s, PTrue)) _)) 
--   = True
-- checkTrueType t 
--   = False

withDepthFill :: SearchMode -> SpecType -> Int -> [(Type, GHC.CoreExpr, Int)] -> SM [CoreExpr]
withDepthFill i t depth tmp = do
  exprs <- fill i depth tmp []
  appDepth <- localMaxAppDepth

  filterElseM (hasType t) exprs $ 
      if depth < appDepth
        then do modify (\s -> s { sExprId = sExprId s + 1 })
                withDepthFill i t (depth + 1) tmp
        else return []

fill :: SearchMode -> Int -> [(Type, GHC.CoreExpr, Int)] -> [CoreExpr] -> SM [CoreExpr] 
fill _ _     []                 accExprs 
  = return accExprs
fill i depth (c : cs) accExprs =  
    case subgoals (fst3 c) of 
      Nothing             -> return [] -- Not a function type
      Just (resTy, subGs) ->
        do  specSubGs <- liftCG $ mapM trueTy (filter (not . isFunction) subGs)
            mapM_ genArgs specSubGs
            em <- sExprMem <$> get
            let argCands  = map (withSubgoal em) subGs
                toGen    = foldr (\x b -> (not . null) x && b) True argCands
            newExprs <- do  curExprId <- sExprId <$> get 
                            trace (" [ fill ] c = " ++ show (snd3 c) ++ " toGen flag " ++ show toGen ++ " Candidate arguments " ++ show argCands) $
                              if toGen 
                                then prune curExprId c argCands
                                else return []
            curExprId <- sExprId <$> get
            let nextEm = map (resTy, , curExprId + 1) newExprs
            modify (\s -> s {sExprMem = nextEm ++ sExprMem s }) 
            let accExprs' = newExprs ++ accExprs
            fill i depth cs accExprs' 

-------------------------------------------------------------------------------------------
-- |                       Pruning terms for function application                      | --
-------------------------------------------------------------------------------------------
type Depth = Int

feasible :: Depth -> (CoreExpr, Int) -> Bool
feasible d c = snd c >= d

feasibles :: Depth -> Int -> [(CoreExpr, Int)] -> [Int]
feasibles _ _ []
  = []
feasibles d i (c:cs) 
  = if feasible d c 
      then i : feasibles d (i+1) cs
      else feasibles d (i+1) cs

isFeasible :: Depth -> [[(CoreExpr, Int)]] -> [[Int]]
isFeasible d =  map (feasibles d 0)

findFeasibles :: Depth -> [[(CoreExpr, Int)]] -> ([[Int]], [Int])
findFeasibles d cs = (fs, ixs)
  where fs  = isFeasible d cs
        ixs = [i | (i, f) <- zip [0..] fs, not (null f)]

toExpr :: [Int] ->                    --  Produced from @isFeasible@.
                                      --   Assumed in increasing order.
          [(GHC.CoreExpr, Int)] ->    --  The candidate expressions.
          ([(GHC.CoreExpr, Int)],     --  Expressions from 2nd argument.
           [(GHC.CoreExpr, Int)])     --  The rest of the expressions
toExpr ixs args = ( [ args !! i | (ix, i) <- is, ix == i ], 
                    [ args !! i | (ix, i) <- is, ix /= i ])
    where is = zip [0..] ixs

fixCands :: Int -> [Int] -> [[(CoreExpr, Int)]] -> ([[(CoreExpr, Int)]], [[(CoreExpr, Int)]])
fixCands i ixs args 
  = let cs = args !! i
        (cur, next)    = toExpr ixs cs
        (args0, args1) = (replace (i+1) cur args, replace (i+1) next args)
    in  (args0, args1)

-- | The first argument should be an 1-based index.
replace :: Int -> a -> [a] -> [a]
replace i x l
  = left ++ [x] ++ right
    where left  = take (i-1) l
          right = drop i l

repeatFix :: [Int] -> [[Int]] -> (Type, CoreExpr, Int) -> [[(CoreExpr, Int)]] -> [CoreExpr] -> SM [CoreExpr]
repeatFix [ ] _ _ _ es 
  = return es
repeatFix (i:is) ixs toFill args es
  = do  let (args0, args1) = fixCands i (ixs !! i) args
        es0 <- fillOne toFill args0
        es1 <- structuralCheck es0
        es2 <- (++ es) <$> filterM isWellTyped es1
        repeatFix is ixs toFill args1 es2

prune :: Depth -> (Type, CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
prune d toFill args 
  = do  let (ixs, is) = findFeasibles d args 
        repeatFix is ixs toFill args []


----------------------------------------------------------------------------
--  | Term generation: Perform type and term application for functions. | --
----------------------------------------------------------------------------

fillOne :: (Type, GHC.CoreExpr, Int) -> [[(CoreExpr, Int)]] -> SM [CoreExpr]
fillOne _ [] 
  = return []
fillOne (t, e, _) cs 
  = applyTerms [e] cs ((snd . fromJust . subgoals) t)

applyTerm :: [GHC.CoreExpr] -> [(CoreExpr, Int)] -> Type -> SM [CoreExpr]
applyTerm es args t = do
  es1 <- mapM (\x -> applyArg es x t) args
  return (concat es1)

applyArg :: [GHC.CoreExpr] -> (CoreExpr, Int) -> Type -> SM [CoreExpr]
applyArg es (arg, _) t 
  = do  !idx <- incrSM
        return  [ case arg of GHC.Var _ -> GHC.App e arg
                              _         ->  let letv = mkVar (Just ("x" ++ show idx)) idx t
                                            in  GHC.Let (GHC.NonRec letv arg) (GHC.App e (GHC.Var letv))
                | e <- es 
                ]

applyTerms :: [GHC.CoreExpr] -> [[(CoreExpr, Int)]] -> [Type] -> SM [CoreExpr]
applyTerms es []     []      
  = return es
applyTerms es0 (c:cs) (t:ts) 
  = do  es1 <- applyTerm es0 c t
        applyTerms es1 cs ts
applyTerms _es _cs _ts 
  = error "[ applyTerms ] Wildcard. " 

--------------------------------------------------------------------------------------
prodScrutinees :: [(Type, CoreExpr, Int)] -> [[[(CoreExpr, Int)]]] -> SM [CoreExpr]
prodScrutinees []     []     = return []
prodScrutinees (c:cs) (a:as) = do 
  es <- fillOne c a
  (++ es) <$> prodScrutinees cs as
prodScrutinees _ _ = error " prodScrutinees "

synthesizeScrutinee :: [Var] -> SM [CoreExpr]
synthesizeScrutinee vars = do
  s <- get
  let foralls = (fst . sCsForalls) s
      insVs = sUniVars s
      fix   = sFix s
      -- Assign higher priority to function candidates that return tuples
      fnCs0 = filter returnsTuple foralls 
      fnCs  = if returnsTuple fix then fix : fnCs0 else fnCs0

      fnEs  = map GHC.Var fnCs
      fnCs' = map (\e -> instantiate e (Just insVs)) fnEs
      sGs   = map ((snd . fromJust) . subgoals . exprType) fnCs'
      argCands = map (map (withSubgoal vs)) sGs
      fnCs'' = map (\e -> (exprType e, e, 0)) fnCs'
      
      vs' = filter ((not . isFunction) . varType) vars
      vs  = map (\v -> (varType v, GHC.Var v, 0)) vs'
  prodScrutinees fnCs'' argCands
