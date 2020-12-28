{-@ LIQUID "--typed-holes" @-}

module ListFoldLength where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ data List [len'] a = N | Cons a (List a) @-}
data List a = N | Cons a (List a)

{-@ measure len' @-}
{-@ len' :: List a -> { v: Int | v >= 0 } @-}
len' :: List a -> Int 
len' N = 0
len' (Cons x xs) = 1 + len' xs

{-@ myFold :: forall a b <p :: x0:List a -> x1:b -> Bool>. 
                (xs:List a -> x:a -> b <p xs> -> b <p (Cons x xs)>) 
              -> b <p N> 
              -> ys:List a
              -> b <p ys>
  @-}
myFold :: (List a -> a -> b -> b) -> b -> List a -> b
myFold op b N           = b
myFold op b (Cons x xs) = op xs x (myFold op b xs) 

{-@ inc :: x: Int -> { v: Int | v = x + 1} @-}
inc :: Int -> Int 
inc x = x + 1

{-@ length' :: xs: List a -> { v: Nat | len' xs == v } @-}
length' :: List a -> Int
length' = _hole
-- length' xs = myFold (\x0 x y -> inc y) 0 xs
