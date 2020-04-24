{-# LANGUAGE CPP           #-}
{-# LANGUAGE TypeOperators #-}

module Data.Group where

import Data.Monoid
#if MIN_VERSION_base(4,7,0)
import Data.Proxy
#endif
#if MIN_VERSION_base(4,9,0)
import Data.Functor.Const
import Data.Functor.Identity
#endif
#if MIN_VERSION_base(4,12,0)
import GHC.Generics
#endif

-- |A 'Group' is a 'Monoid' plus a function, 'invert', such that:
--
-- @a \<> invert a == mempty@
--
-- @invert a \<> a == mempty@
class Monoid m => Group m where
  invert :: m -> m

  -- | Group subtraction: @x ~~ y == x \<> invert y@
  (~~) :: m -> m -> m
  x ~~ y = x `mappend` invert y

  -- |@'pow' a n == a \<> a \<> ... \<> a @
  --
  -- @ (n lots of a) @
  --
  -- If n is negative, the result is inverted.
  pow :: Integral x => m -> x -> m
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

infixl 7 ~~

instance Group () where
  invert () = ()
  pow _ _ = ()

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
-- @a \<> b == b \<> a@
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


-- | A 'Group' G is 'Cyclic' if there exists an element x of G such that for all y in G, there exists an n, such that
--
-- @y = pow x n@
class Group a => Cyclic a where
  generator :: a

generated :: Cyclic a => [a]
generated =
  iterate (mappend generator) mempty

instance Cyclic () where
  generator = ()

#if MIN_VERSION_base(4,7,0)
-- | Trivial group, Functor style.
instance Group (Proxy x) where
  invert _ = Proxy
  _ ~~ _ = Proxy
  pow _ _ = Proxy

instance Abelian (Proxy x)

instance Cyclic (Proxy x) where
  generator = Proxy
#endif

-- 'Const' has existed for a long time, but the Monoid instance
-- arrives in base-4.9.0.0. Similarly, 'Identity' was defined in
-- base-4.8.0.0 but doesn't get the Monoid instance until base-4.9.0.0
#if MIN_VERSION_base(4,9,0)
-- | 'Const' lifts groups into a functor.
instance Group a => Group (Const a x) where
  invert (Const a) = Const (invert a)
  Const a ~~ Const b = Const (a ~~ b)

-- | 'Identity' lifts groups pointwise (at only one point).
instance Group a => Group (Identity a) where
  invert (Identity a) = Identity (invert a)
  Identity a ~~ Identity b = Identity (a ~~ b)

instance Abelian a => Abelian (Const a x)

instance Abelian a => Abelian (Identity a)

instance Cyclic a => Cyclic (Const a x) where
  generator = Const generator

instance Cyclic a => Cyclic (Identity a) where
  generator = Identity generator
#endif

-- (:*:) and (:.:) exist since base-4.6.0.0 but the Monoid instances
-- arrives in base-4.12.0.0.
#if MIN_VERSION_base(4,12,0)
-- | Product of groups, Functor style.
instance (Group (f a), Group (g a)) => Group ((f :*: g) a) where
  invert (a :*: b) = invert a :*: invert b
  (a :*: b) ~~ (c :*: d) = (a ~~ c) :*: (b ~~ d)

-- See https://gitlab.haskell.org/ghc/ghc/issues/11135#note_111802 for the reason Compose is not also provided.
-- Base does not define Monoid (Compose f g a) so this is the best we can
-- really do for functor composition.
instance Group (f (g a)) => Group ((f :.: g) a) where
  invert (Comp1 xs) = Comp1 (invert xs)
  Comp1 xs ~~ Comp1 ys = Comp1 (xs ~~ ys)

instance (Abelian (f a), Abelian (g a)) => Abelian ((f :*: g) a)

instance Abelian (f (g a)) => Abelian ((f :.: g) a)
#endif
