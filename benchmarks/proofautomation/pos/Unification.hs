-- | Unification for simple terms a la Zombie
-- | cite : http://www.seas.upenn.edu/~sweirich/papers/congruence-extended.pdf

-- RJ: for some odd reason, this file NEEDs cuts/qualifiers. It is tickled by
-- nonlinear-cuts (i.e. they add new cut vars that require qualifiers.) why?
-- where? switch off non-lin-cuts in higher-order mode?

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate=all"   @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
{-@ LIQUID "--debug-instantiation" @-}

module Unify where

import Language.Haskell.Liquid.ProofCombinators
import qualified  Data.Set as S

-- | Data Types
data Term = TBot | TVar Int | TFun Term Term
  deriving (Eq)
{-@ data Term [tsize] @-}

type Substitution = L (P Int Term)
data P a b = P a b

-- | Unification
-- | If unification succeds then the returned substitution makes input terms equal
-- | Unification may fail with Nothing, or diverge

{-@ Lazy unify @-}
{-@ unify :: t1:Term -> t2:Term
          -> Maybe {θ:Substitution | apply θ t1 == apply θ t2 } @-}
unify :: Term -> Term -> Maybe Substitution
unify TBot TBot
  = Just Emp
unify t1@(TVar i) t2
  | not (S.member i (freeVars t2))
  = Just (C (P i t2) Emp `byTheorem` theoremVar t2 i)
unify t1 t2@(TVar i)
  | not (S.member i (freeVars t1))
  = Just (C (P i t1) Emp `byTheorem` theoremVar t1 i)
unify (TFun t11 t12) (TFun t21 t22)
  = case unify t11 t21 of
      Just θ1 -> case unify (apply θ1 t12) (apply θ1 t22) of
                   Just θ2 -> Just (append θ2 θ1 `byTheorem` theoremFun t11 t12 t21 t22 θ1 θ2)
                   Nothing -> Nothing
      _       -> Nothing
unify t1 t2
  = Nothing


-- | Helper Functions

{-@ measure freeVars @-}
freeVars :: Term -> S.Set Int
freeVars TBot = S.empty
freeVars (TFun t1 t2) = S.union (freeVars t1) (freeVars t2)
freeVars (TVar i)     = S.singleton i


{-@ axiomatize apply @-}
apply :: Substitution -> Term -> Term
apply s t
  | llen s == 0
  = t
  | otherwise
  = applyOne (hd s) (apply (tl s) t)

{-@ axiomatize applyOne @-}
applyOne :: (P Int Term) -> Term -> Term
applyOne su t
  | isTVar t, fromTVar t == myfst su
  = mysnd su
  | isTFun t
  = TFun (applyOne su (tfunArg t)) (applyOne su (tfunRes t))
  | otherwise
  = t


-- | Proving the required theorems

{-@ automatic-instances theoremFun @-}

theoremFun :: Term -> Term -> Term -> Term -> Substitution -> Substitution -> Proof
{-@ theoremFun
  :: t11:Term
  -> t12:Term
  -> t21:Term
  -> t22:Term
  -> s1:{θ1:Substitution | apply θ1 t11 == apply θ1 t21 }
  -> s2:{θ2:Substitution | apply θ2 (apply s1 t12) == apply θ2 (apply s1 t22) }
  -> { apply (append s2 s1) (TFun t11 t12) ==
       apply (append s2 s1) (TFun t21 t22)  }
  @-}
theoremFun t11 t12 t21 t22 θ1 θ2
  =   split_fun t11 t12 (append θ2 θ1)
  &&& append_apply θ2 θ1 t11
  &&& append_apply θ2 θ1 t12
  &&& append_apply θ2 θ1 t21
  &&& append_apply θ2 θ1 t22
  &&& split_fun t21 t22 (append θ2 θ1)


{-@ automatic-instances split_fun with 1 @-}

split_fun :: Term -> Term -> Substitution -> Proof
{-@ split_fun :: t1:Term -> t2:Term -> θ:Substitution
   -> {apply θ (TFun t1 t2) == TFun (apply θ t1) (apply θ t2)} / [llen θ] @-}
split_fun t1 t2 Emp
  = trivial
split_fun t1 t2 (C su θ)
   = split_fun t1 t2 θ 

{-@ automatic-instances append_apply  @-}

append_apply :: Substitution -> Substitution -> Term -> Proof
{-@ append_apply
   :: θ1:Substitution
   -> θ2:Substitution
   -> t :Term
   -> {apply θ1 (apply θ2 t) == apply (append θ1 θ2) t}
  @-}
append_apply Emp θ2 t
  = trivial
append_apply (C su θ) θ2 t
  = append_apply θ θ2 t --  &&&  append_len θ θ2

{-@ automatic-instances append_len  @-}

{-@ append_len ::  s1:Substitution -> s2:Substitution -> {llen (append s1 s2) == llen s1 + llen s2  } @-}
append_len ::  Substitution -> Substitution -> Proof
append_len Emp _       = trivial 
append_len (C _ s1) s2 = append_len s1 s2 


{-@ automatic-instances append_len  @-}


{-@ automatic-instances theoremVar  @-}

{-@ theoremVar :: t:Term
             -> i:{Int | not (Set_mem i (freeVars t)) }
             -> {apply (C (P i t) Emp) (TVar i) == apply (C (P i t) Emp) t } @-}
theoremVar :: Term -> Int ->Proof
theoremVar t i
  =   theoremVarOne t i t

{-@ automatic-instances theoremVarOne  @-}

{-@ theoremVarOne :: t:Term
             -> i:{Int | not (Set_mem i (freeVars t)) }
             -> ti:Term
             -> { t == applyOne (P i ti) t } @-}
theoremVarOne :: Term -> Int -> Term -> Proof
theoremVarOne (TFun t1 t2) i ti
  = theoremVarOne t1 i ti &&& theoremVarOne t2 i ti
theoremVarOne t i ti
  = trivial



-- | Helpers to lift Terms and Lists into logic...
-- | With some engineering all these can be automated...
-- | Lifting Terms into logic
{-@ measure tsize @-}
tsize :: Term -> Int
{-@ invariant {t:Term | tsize t >= 0 } @-}

-- NV TODO: something goes wrong with measure invariants
{-@ tsize :: Term -> Int  @-}
tsize TBot     = 0
tsize (TVar _) = 0
tsize (TFun t1 t2) = 1 + (tsize t1) + (tsize t2)

{-@ measure isTBot @-}
{-@ measure isTVar @-}
{-@ measure isTFun @-}

isTBot, isTVar, isTFun :: Term -> Bool
isTBot TBot = True
isTBot _    = False

isTVar (TVar _) = True
isTVar _        = False

isTFun (TFun _ _) = True
isTFun _          = False

{-@ measure tfunArg @-}
{-@ measure tfunRes @-}
tfunArg, tfunRes :: Term -> Term
{-@ tfunArg, tfunRes :: t:{Term | isTFun t} -> {v:Term | tsize v < tsize t} @-}
tfunArg (TFun t _) = t
tfunRes (TFun _ t) = t

{-@ measure fromTVar @-}
{-@ fromTVar :: {t:Term | isTVar t} -> Int @-}
fromTVar :: Term -> Int
fromTVar (TVar i) = i


{-@ measure myfst @-}
{-@ measure mysnd @-}
myfst :: (P a b) -> a
myfst (P x _) = x
mysnd :: (P a b) -> b
mysnd (P _ x) = x


-- | List Helpers
{-@ axiomatize append @-}
{-@ append :: xs:L a -> ys:L a -> {v:L a | llen v == llen xs + llen ys } @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = C (hd xs) (append (tl xs) ys)

data L a = Emp | C a (L a)
{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen Emp      = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs