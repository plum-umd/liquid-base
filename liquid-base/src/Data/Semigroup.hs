{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                )

import           Data.List
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NonEmpty
import qualified Liquid.ProofCombinators as P

class Semigroup a where
    {-@ mappend :: a -> a -> a @-}
    mappend :: a -> a -> a
    sconcat :: NonEmpty a -> a

class Semigroup a => VSemigroup a where
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {mappend (mappend v v') v'' == mappend v (mappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()

    {-@ lawSconcat :: ys:NonEmpty a -> {foldr mappend (NonEmpty.head' ys) (NonEmpty.tail' ys) == sconcat ys} @-}
    lawSconcat :: NonEmpty a -> ()

class Semigroup a => Monoid a where
    {-@ mempty :: a @-}
    mempty :: a

    mconcat :: List a -> a

class (VSemigroup a, Monoid a) => VMonoid a where
    {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
    lawEmpty :: a -> () -- JP: Call this lawIdentity?

    {-@ lawMconcat :: xs:List a -> {mconcat xs = foldr mappend mempty xs} @-}
    lawMconcat :: List a -> ()
-- Natural Numbers



data Sum a = Sum {getSum :: a}

instance Num a => Semigroup (Sum a) where
  mappend (Sum x) (Sum y) = Sum $ x + y
  sconcat (NonEmpty h t) = foldr mappend h t

instance Num a => VSemigroup (Sum a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  mconcat = foldr mappend mempty

data Product a = Product {getProduct :: a}

instance Num a => Semigroup (Product a) where
  mappend (Product x) (Product y) = Product $ x * y
  sconcat (NonEmpty h t) = foldr mappend h t

instance Num a => VSemigroup (Product a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Num a => Monoid (Product a) where
  mempty = Product 1
  mconcat = foldr mappend mempty



{-@ reflect flip @-}
{-@ reflect composeEndo @-}
composeEndo :: (b -> a -> a) -> b -> Endo a
composeEndo f x = Endo (f x)

flip :: (a -> b -> c) -> b -> a -> c
flip f y x = f x y

{-@ reflect dualEndoFlip @-}
dualEndoFlip :: (a -> b -> a) -> b -> Dual (Endo a)
dualEndoFlip f x  = Dual (Endo (flip f x))
class Foldable t where
  {-@ foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m @-}
  foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m
  foldr :: (a -> b -> b) -> b -> t a -> b
--  foldl :: (b -> a -> b) -> b -> t a -> b

-- class Foldable t => VFoldable t where
--   {-@ lawFoldable1 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr f z t == appEndo (foldMap (composeEndo f) t ) z} @-}
--   lawFoldable1 :: forall a b . (a -> b -> b) -> b -> t a -> ()
-- --  {-@ lawFoldable2 :: forall a b. f:(b -> a -> b) -> z:b -> t:t a -> {foldl f z t = appEndo (getDual (foldMap (dualEndoFlip f) t)) z} @-}
-- --  lawFoldable2 :: forall a b. (b -> a -> b) -> b -> t a -> ()
-- --  {-@ lawFoldable3 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr' f z t = foldMap id' f z t} @-}
-- --  lawFoldable3 :: forall a b . (a -> b -> b) -> b -> t a -> ()

-- data Id a = Id a

-- instance Foldable Maybe where
--   foldMap f Nothing = mempty
--   foldMap f (Just x) = f x
--   foldr f m Nothing = m
--   foldr f m (Just x) = f x m
--   -- foldl f m Nothing = m
--   -- foldl f m (Just x) = f m x

-- instance VFoldable Maybe where
--   lawFoldable1 _ _ Nothing = ()
--   lawFoldable1 _ _ _ = ()
--   -- lawFoldable2 _ _ Nothing = ()
--   -- lawFoldable2 _ _ _ = ()

-- instance Foldable Id where
--   foldMap f (Id a) = f a
--   foldr f m (Id a) = f a m

-- instance VFoldable Id where
--   lawFoldable1 _ _ _ = ()

-- data Const a b = Const {getConst :: a}

-- instance Foldable (Const a) where
--   foldr f m _ = m
--   foldMap _ _ = mempty

-- instance VFoldable (Const a) where
--   lawFoldable1 _ _ _ = ()

-- data Complex a = Complex a a

-- instance Foldable Complex where
--   foldMap f (Complex a b) = f a `mappend` f b
--   foldr f m (Complex a b) = f a (f b m)

-- instance VFoldable Complex where
--   lawFoldable1 _ _ _ = ()

-- instance Foldable List where
--   foldr f z Nil = z
--   foldr f z (Cons x xs) = f x (foldr f z xs)
--   foldMap f Nil = mempty
--   foldMap f (Cons x xs) = f x `mappend` foldMap f xs

-- instance VFoldable List where
--   lawFoldable1 f z Nil  = ()
--   lawFoldable1 f z (Cons x xs) = lawFoldable1 f z xs `P.cast` ()
