{-@ LIQUID "--typed-holes" @-}

module ScrutineeSynSimple where

import qualified Data.Set as S

import Language.Haskell.Liquid.Synthesize.Error

{-@ inline abs' @-}
{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int 
abs' x = if x >= 0 then x else -x

{-@ split :: xs: [a] -> 
    { v: ( { v: [a] | abs' (len xs - 2 * len v) <= 1 }, [a])
                      | len xs == len (fst v) + len (snd v) &&
                        listElts xs == S.union (listElts (fst v)) (listElts (snd v)) }
 @-}
split :: [a] -> ([a], [a])
split xs = 
    case xs of 
        [] -> (xs, xs)
        x5:x6 -> 
            case x6 of
                [] -> (x6, xs)
                x11:x12 ->
                    case split x12 of
                        (x16, x17) -> (x11:x16, x5:x17)


{-@ caseSplit1 :: xs: [a] -> { v: [a] | abs' (2 * len v - len xs) <= 1 } @-}
caseSplit1 :: [a] -> [a]
caseSplit1 x_S0 =
    case x_S0 of
        [] -> x_S0
        (:) x_Sb x_Sc ->
            case split x_S0 of
                (,) x_S2z x_S2A -> x_S2A
