{-# LANGUAGE RecordWildCards #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--typed-holes" @-}

module MultipleHoles where

import Language.Haskell.Liquid.Synthesize.Error

data IntRange = IntRange {
      lower :: Int
    , upper :: Int
    }
    -- deriving (Show)

{-@ reflect betweenInt @-}
betweenInt :: Int -> IntRange -> Bool
betweenInt x IntRange{..} = lower < x && x < upper

{-@ reflect subsetInt @-}
subsetInt :: IntRange -> IntRange -> Bool
subsetInt (IntRange l1 u1) (IntRange l2 u2) = l1 >= l2 && u1 <= u2

{-@
data Loc = Loc {
      x :: Int
    , y :: Int
    }
@-}
data Loc = Loc {
      x :: Int
    , y :: Int
    }
    -- deriving (Show)

data LocRange = LocRange {
      xD :: IntRange
    , yD :: IntRange
    }
    -- deriving (Show)

{-@ reflect betweenLoc @-}
betweenLoc :: Loc -> LocRange -> Bool
betweenLoc Loc{..} LocRange{..} = betweenInt x xD && betweenInt y yD

{-@ reflect subsetLoc @-}
subsetLoc :: LocRange -> LocRange -> Bool
subsetLoc (LocRange x1 y1) (LocRange x2 y2) = subsetInt x1 x2 && subsetInt y1 y2

{-@
data Ship = Ship {
      shipCapacity :: Int
    , shipLoc :: Loc
    }
@-}
data Ship = Ship {
      shipCapacity :: Int
    , shipLoc :: Loc
    }
    -- deriving (Show)

{-@ reflect betweenShip @-}
betweenShip :: Ship -> ShipRange -> Bool
betweenShip Ship{..} ShipRange{..} = betweenInt shipCapacity shipCapacityD && betweenLoc shipLoc shipLocD

{-@ reflect subsetShip @-}
subsetShip :: ShipRange -> ShipRange -> Bool
subsetShip (ShipRange c1 l1) (ShipRange c2 l2) = subsetInt c1 c2 && subsetLoc l1 l2


data ShipRange = ShipRange {
      shipCapacityD :: IntRange
    , shipLocD :: LocRange
    } 
    -- deriving (Show)

{-@ reflect atLeast @-}
atLeast :: Ship -> Bool
atLeast z = shipCapacity z > b
    where
        b = 50

{-@ reflect abs' @-}
abs' :: Int -> Int
abs' i | i < 0 = -1 * i
abs' i         = i

{-@ reflect nearby @-}
nearby :: Ship -> Bool
nearby (Ship _ z) = abs' (x z - x l) + abs' (y z - y l) <= d
    where
        l = Loc 200 200
        d = 100

{-@ reflect ok @-}
ok :: Ship -> Bool
ok z = atLeast z && nearby z

{-@ fifty :: { v: Int | v == 50 } @-}
fifty :: Int
fifty = 50

{-@ fiftyOne :: { v: Int | v == 51 } @-}
fiftyOne :: Int
fiftyOne = 51

{-@ max' :: x: Int -> y: Int -> { v: Int | v == if x >= y then x else y } @-}
max' :: Int -> Int -> Int
max' a b = if a >= b then a else b

{-@ min' :: x:Int -> y:Int -> { v: Int | v == if x <= y then x else y } @-}
min' :: Int -> Int -> Int
min' a b = if a <= b then a else b


{-@ adversary 
      :: secret:Ship 
      -> {prior: ShipRange | betweenShip secret prior} 
      -> {response: Bool | response == atLeast secret} 
      -> {post: ShipRange | betweenShip secret post && subsetShip post prior} 
  @-}
adversary :: Ship -> ShipRange -> Bool -> ShipRange
adversary secret shipRange b = 
    case shipRange of
        ShipRange range loc -> 
            case range of 
                IntRange l u -> 
                    case b of
                        True  -> ShipRange (IntRange (max _fifty l) u) loc
                        False -> ShipRange (IntRange l (min fiftyOne u)) loc

-- adversarySound1 secret shipRange b = 
--     case shipRange of
--         ShipRange range loc -> 
--             case range of 
--                 IntRange l u -> 
--                     case b of
--                         True  -> ShipRange (IntRange (max' fifty l) u) loc
--                         False -> ShipRange (IntRange l (min' fiftyOne u)) loc
