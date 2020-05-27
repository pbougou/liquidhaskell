{-@ LIQUID "--typed-holes" @-}

module ListZipWith where

import Language.Haskell.Liquid.Synthesize.Error

{-@ zipWith' :: f: (a -> b -> c) 
               -> xs: [a] 
               -> { ys: [b] | len ys == len xs} 
               -> {v: [c] | len v == len xs } 
@-}
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' x_S0 x_S1 x_S2 =
    case x_S1 of
        [] -> []
        (:) x_Sv x_Sw ->
            case x_S2 of
                [] -> error " Dead code! "
                (:) x_S1f x_S1g -> (:) (x_S0 x_Sv x_S1f) (zipWith' x_S0 x_Sw x_S1g)