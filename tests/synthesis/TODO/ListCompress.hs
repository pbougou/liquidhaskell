{-@ LIQUID "--typed-holes" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module ListCompress where

import qualified Data.Set as S
import Language.Haskell.Liquid.Synthesize.Error

{-@ type CList a = [a]<{\h t -> h /= t}> @-}
type CList a = List a

{-@ compress :: x: [a] -> { v: CList a | listElts v == listElts x } @-}
compress :: Eq a => [a] -> CList a
-- compress = _goal
compress xs = 
    case xs of
        [] -> []
        x3:x4 -> 
            case compress x4 of
                [] -> [x3]
                x10:x11 ->
                    if x3 == x10
                        then compress x4
                        else x3:(x10:x11)



