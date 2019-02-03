module Ratio

%access public export

-- TODO: This could probably all be better...

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
    (.%) : (Integral a, Eq a, Abs a, Ord a, Neg a) => a -> a -> Ratio a

infixl 7 :%
(:%) : (Integral a, Eq a, Abs a, Ord a, Neg a) =>
  a -> a -> Maybe (Ratio a)
(:%) n m =
  case m == 0 of
    False =>
        let cd = gcd n m
            num = (n `div` cd) -- TODO: Should be `quot`?
            den = (m `div` cd) -- TODO: Should be `quot`?
        in Just $ num .% den
    True => Nothing

Rational : Type
Rational = Ratio Integer

numerator : Ratio a -> a
numerator (n .% _) = n

denominator : Ratio a -> a
denominator (_ .% d) = d

Eq a => Eq (Ratio a) where
  (a .% b) == (c .% d) = (a * d) == (c * b)

Ord a => Ord (Ratio a) where
  compare (a .% b) (c .% d) = compare (a * d) (c * b)



rationalDiv : Ratio a -> Ratio a -> Maybe (Ratio a)
rationalDiv (a .% b) (c .% d) = (a * d) :% (b * c)

-- rationalMod : Ratio a -> Ratio a -> Maybe (Ratio a)
-- rationalMod a b = (a - b) * a `div` b

rationalAdd : Ratio a -> Ratio a -> Maybe (Ratio a)
rationalAdd (a .% b) (c .% d) = ((a * d) + (b * c)) :% (b * d)

rationalMul : Ratio a -> Ratio a -> Maybe (Ratio a)
rationalMul (a .% b) (c .% d) = (a * c) :% (b * d)

rationalFromInteger : Integer -> Maybe (Ratio Integer)
rationalFromInteger i = (fromInteger i) :% 1

rationalNegate : Ratio a -> Maybe (Ratio a)
rationalNegate (a .% b) = (negate a) :% b

rationalSub : Ratio a -> Ratio a -> Maybe (Ratio a)
rationalSub (a .% b) (c .% d) = ((a * d) - (c * b)) :% (b * d)

Show a => Show (Ratio a) where
    show (n .% d) = show n ++ " % " ++ show d

rationalCast : Rational -> Maybe Double
rationalCast (a .% b) =
  case b == 0 of
    False => Just $ (cast a) / (cast b)
    True => Nothing
