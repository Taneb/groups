{-|
Module      : Data.Group
Copyright   : (C) 2013 Nathan van Doorn
License     : BSD-3
Maintainer  : nvd1234@gmail.com

The laws for 'RegularSemigroup' and 'InverseSemigroup' are from
<https://www.youtube.com/watch?v=HGi5AxmQUwU Ed Kmett's talk at Lambda World 2018>.
-}

module Data.Group where

import Data.Monoid

-- | A 'RegularSemigroup' is a 'Semigroup' where every element @x@ has
-- at least one element @inv x@ such that:
--
-- @
--     x \<> 'inv' x \<>     x =     x
-- 'inv' x \<>     x \<> 'inv' x = 'inv' x
-- @
class Semigroup g => RegularSemigroup g where
  inv :: g -> g

-- | An 'InverseSemigroup' is a 'RegularSemigroup' with the additional
-- restriction that inverses are unique.
--
-- Equivalently:
--
-- 1. Any idempotent @y@ is of the form @x \<> inv x@ for some x.
-- 2. All idempotents commute. (<https://math.stackexchange.com/questions/1093328/do-the-idempotents-in-an-inverse-semigroup-commute/1093476#1093476 Partial proof>)
class RegularSemigroup g => InverseSemigroup g

-- | A 'Group' adds the conditions that:
--
-- @
-- a     \<> 'inv' a == 'mempty'
-- 'inv' a \<>     a == 'mempty'
-- @
class (InverseSemigroup g, Monoid g) => Group g where
  invert :: g -> g
  invert = inv

  -- |@'pow' a n == a \<> a \<> ... \<> a @
  --
  -- @ (n lots of a) @
  --
  -- If n is negative, the result is inverted.
  pow :: Integral x => g -> x -> g
  pow x0 n0 = case compare n0 0 of
    LT -> invert . f x0 $ negate n0
    EQ -> mempty
    GT -> f x0 n0
    where
      f x n
        | even n = f (x `mappend` x) (n `quot` 2)
        | n == 1 = x
        | otherwise = g (x `mappend` x) (n `quot` 2) x
      g x n c
        | even n = g (x `mappend` x) (n `quot` 2) c
        | n == 1 = x `mappend` c
        | otherwise = g (x `mappend` x) (n `quot` 2) (x `mappend` c)
{-# DEPRECATED invert "use inv from RegularSemigroup instead" #-}

instance RegularSemigroup () where
  inv () = ()

instance Num a => RegularSemigroup (Sum a) where
  inv = Sum . negate . getSum

instance Fractional a => RegularSemigroup (Product a) where
  inv = Product . recip . getProduct

instance RegularSemigroup a => RegularSemigroup (Dual a) where
  inv = Dual . inv . getDual

instance RegularSemigroup b => RegularSemigroup (a -> b) where
  inv f = inv . f

instance (RegularSemigroup a, RegularSemigroup b) => RegularSemigroup (a, b) where
  inv (a, b) = (inv a, inv b)

instance (RegularSemigroup a, RegularSemigroup b, RegularSemigroup c) => RegularSemigroup (a, b, c) where
  inv (a, b, c) = (inv a, inv b, inv c)

instance (RegularSemigroup a, RegularSemigroup b, RegularSemigroup c, RegularSemigroup d) => RegularSemigroup (a, b, c, d) where
  inv (a, b, c, d) = (inv a, inv b, inv c, inv d)

instance (RegularSemigroup a, RegularSemigroup b, RegularSemigroup c, RegularSemigroup d, RegularSemigroup e) => RegularSemigroup (a, b, c, d, e) where
  inv (a, b, c, d, e) = (inv a, inv b, inv c, inv d, inv e)

instance InverseSemigroup ()
instance Num a => InverseSemigroup (Sum a)
instance Fractional a => InverseSemigroup (Product a)
instance InverseSemigroup a => InverseSemigroup (Dual a)
instance InverseSemigroup b => InverseSemigroup (a -> b)
instance (InverseSemigroup a, InverseSemigroup b) => InverseSemigroup (a, b)
instance (InverseSemigroup a, InverseSemigroup b, InverseSemigroup c) => InverseSemigroup (a, b, c)
instance (InverseSemigroup a, InverseSemigroup b, InverseSemigroup c, InverseSemigroup d) => InverseSemigroup (a, b, c, d)
instance (InverseSemigroup a, InverseSemigroup b, InverseSemigroup c, InverseSemigroup d, InverseSemigroup e) => InverseSemigroup (a, b, c, d, e)

instance Group () where
  invert () = ()
  pow () _ = ()

instance Num a => Group (Sum a) where
  invert = Sum . negate . getSum
  {-# INLINE invert #-}
  pow (Sum a) b = Sum (a * fromIntegral b)

instance Fractional a => Group (Product a) where
  invert = Product . recip . getProduct
  {-# INLINE invert #-}
  pow (Product a) b = Product (a ^^ b)

instance Group a => Group (Dual a) where
  invert = Dual . invert . getDual
  {-# INLINE invert #-}
  pow (Dual a) n = Dual (pow a n)

instance Group b => Group (a -> b) where
  invert f = invert . f
  pow f n e = pow (f e) n

instance (Group a, Group b) => Group (a, b) where
  invert (a, b) = (invert a, invert b)
  pow (a, b) n = (pow a n, pow b n)

instance (Group a, Group b, Group c) => Group (a, b, c) where
  invert (a, b, c) = (invert a, invert b, invert c)
  pow (a, b, c) n = (pow a n, pow b n, pow c n)

instance (Group a, Group b, Group c, Group d) => Group (a, b, c, d) where
  invert (a, b, c, d) = (invert a, invert b, invert c, invert d)
  pow (a, b, c, d) n = (pow a n, pow b n, pow c n, pow d n)

instance (Group a, Group b, Group c, Group d, Group e) => Group (a, b, c, d, e) where
  invert (a, b, c, d, e) = (invert a, invert b, invert c, invert d, invert e)
  pow (a, b, c, d, e) n = (pow a n, pow b n, pow c n, pow d n, pow e n)

-- |An 'Abelian' group is a 'Group' that follows the rule:
--
-- @
-- a \<> b == b \<> a
-- @
class Group g => Abelian g

instance Abelian ()

instance Num a => Abelian (Sum a)

instance Fractional a => Abelian (Product a)

instance Abelian a => Abelian (Dual a)

instance Abelian b => Abelian (a -> b)

instance (Abelian a, Abelian b) => Abelian (a, b)

instance (Abelian a, Abelian b, Abelian c) => Abelian (a, b, c)

instance (Abelian a, Abelian b, Abelian c, Abelian d) => Abelian (a, b, c, d)

instance (Abelian a, Abelian b, Abelian c, Abelian d, Abelian e) => Abelian (a, b, c, d, e)

-- | A 'Group' G is 'Cyclic' if there exists an element x of G such
-- that for all y in G, there exists an n, such that:
--
-- @
-- y = pow x n
-- @
class Group a => Cyclic a where
  generator :: a

generated :: Cyclic a => [a]
generated =
  iterate (mappend generator) mempty
