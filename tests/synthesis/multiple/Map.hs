{-@ LIQUID "--typed-holes" @-}

module Map where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ myMap :: (a -> b) -> xs:[a] -> {v:[b] | len v == len xs} @-}
myMap :: (a -> b) -> [a] -> [b]
myMap f xs0 = 
    case xs0 of 
        [] -> []
        (x:xs) -> _other
-- map f [] = []
-- map f (x:xs) = f x : map f xs