{-@ LIQUID "--typed-holes" @-}

module ListZip where 

import Language.Haskell.Liquid.Synthesize.Error

{-@ zip' :: xs: [a] -> {ys:[b] | len ys == len xs} -> {v:[(a, b)] | len v == len xs} @-}
zip' :: [a] -> [b] -> [(a, b)]
zip' x_S0 x_S1 =
    case x_S0 of
        [] -> []
        (:) x_Sn x_So ->
            case x_S1 of
                [] -> error " Dead code! "
                (:) x_S16 x_S17 -> (:) (x_Sn, x_S16) (zip' x_So x_S17)