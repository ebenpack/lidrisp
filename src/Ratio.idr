module Ratio

import Data.ZZ
import Data.PosNat

%access public export

-- TODO: This could probably be better...

gcd : (Integral a, Abs a, Eq a) => a -> a -> a
gcd n m = gcd' (abs n) (abs m)
    where
        gcd' : a -> a -> a
        gcd' n m =
            if m == 0
                then n
                else gcd' m (n `mod` m)

nonZero : (Integral a, Eq a) => a -> Bool
nonZero n = n /= 0

infixl 7 .%
data Ratio : Type -> Type where
    (.%) : (Integral a, Eq a, Abs a, Ord a) => a -> a -> Ratio a

Rational : Type
Rational = Ratio Integer

infixl 7 :%
(:%) : (Integral a, Eq a, Abs a, Ord a) => a -> (m:a) -> {auto prf : nonZero m = True} -> Ratio a
(:%) n m = case m == 0 of
    False =>
        let cd = gcd n m
            num = (n `div` cd) -- TODO: Should be `quot`?
            den = (m `div` cd) -- TODO: Should be `quot`?
        in (.%) num den

numerator : Ratio a -> a
numerator (n .% _) = n

denominator : Ratio a -> a
denominator (_ .% d) = d

Eq a => Eq (Ratio a) where
    (a .% b) == (c .% d) = (a * d) == (c * b)

Ord a => Ord (Ratio a) where
    compare (a .% b) (c .% d) = compare (a * d) (c * b)

-- (Integral a, Eq a, Abs a, Ord a) => Num (Ratio a) where
--     (a .% b) + (c .% d) = ((a * d) + (b * c)) :% (b * d)
--     (a .% b) * (c .% d) = (a * c) :% (b * d)
--     fromInteger i = (fromInteger i) :% 1
--
-- Neg a => Neg (Ratio a) where
--     negate (a .% b) = (negate a) :% b
--     (a .% b) - (b .% c) = ((a * d) - (b * c)) :% (b * d)
--
-- Integral a => Integral (Ratio a) where
--     div (a .% b) (c .% d) = (a * d) :% (b * c)
--     mod a b = (a - b) * a `div` b


Show a => Show (Ratio a) where
    show (n .% d) = show n ++ " % " ++ show d

Cast Rational Double where
    cast n = (cast $ numerator n) / (cast $ denominator n)
