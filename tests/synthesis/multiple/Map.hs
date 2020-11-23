{-@ LIQUID "--typed-holes" @-}

module Map where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ myMap :: (Int -> Bool) -> xs:[Int] -> {v:[Bool] | len v == len xs} @-}
myMap :: (Int -> Bool) -> [Int] -> [Bool]
myMap f xs0 = 
    case xs0 of 
        [] -> _empty
        (x:xs) -> _other
-- map f [] = []
-- map f (x:xs) = f x : map f xs