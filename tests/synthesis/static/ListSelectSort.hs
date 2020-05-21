{-@ LIQUID "--typed-holes" @-}

module ListSelectSort where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ data IList a = N | ICons { x :: a, xs :: IList { v: a | x <= v } } @-}
data IList a = N | ICons a (IList a)

{-@ measure iLen @-}
{-@ iLen :: IList a -> Nat @-}
iLen :: IList a -> Int
iLen N = 0
iLen (ICons x xs) = 1 + iLen xs

{-@ measure iElts @-}
{-@ iElts :: IList a -> S.Set a @-}
iElts :: Ord a => IList a -> S.Set a
iElts N = S.empty
iElts (ICons x xs) = S.union (S.singleton x) (iElts xs)


{-@ type MinPair a = (x::a, [ { y: a | x <= y } ]) @-}
type MinPair a = (a, [a])

{-@ measure minP @-}
{-@ minP :: MinPair a -> a @-}
minP :: MinPair a -> a
minP (x, l) = x
  
{-@ measure rest @-} 
{-@ rest :: MinPair a -> [a] @-}
rest :: MinPair a -> [a]
rest (x, l) = l

{-@ extractMin :: { xs: [a] | len xs > 0 } 
            -> { v: MinPair a | listElts xs == S.union (S.singleton (minP v)) (listElts (rest v)) && 
                                len xs == 1 + len (rest v) }
  @-}
extractMin :: Ord a => [a] -> (a, [a])
extractMin [x]    = (x, [])
extractMin (x:xs) = 
    let (y, ys) = extractMin xs
    in  if x <= y then (x, y:ys) else (y, x:ys)

{-@ selectSort :: xs: [a] -> { v: IList a | iElts v == listElts xs } @-}
selectSort :: Ord a => [a] -> IList a
selectSort x_S1 =
    case x_S1 of
        [] -> N
        (:) x_Se x_Sf ->
            case extractMin x_S1 of
                (,) x_S1d x_S1e -> ICons x_S1d (selectSort x_S1e)