{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Foldable.Classes where
import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , flip
                                                , tail
                                                , Maybe (..)
                                                , Foldable (..)
                                                , id
                                                )

import Data.Semigroup.Classes
import Liquid.ProofCombinators
import Data.Endo
import Data.Functor.Identity
import Data.Dual
import Data.Function
import Data.List
import Data.List.NonEmpty
import Data.Maybe
import Data.Functor.Const

{-@ reflect composeEndo @-}
composeEndo :: (b -> a -> a) -> b -> Endo a
composeEndo f x = Endo (f x)

{-@ reflect dualEndoFlip @-}
dualEndoFlip :: (a -> b -> a) -> b -> Dual (Endo a)
dualEndoFlip f x  = Dual (Endo (flip f x))


instance Semigroup (Endo a) where
  mappend (Endo f) (Endo g) = Endo (compose f g)
  sconcat (NonEmpty h t) = foldlList mappend h t


instance VSemigroup (Endo a) where
  lawAssociative (Endo f) (Endo g) (Endo h) = composeAssoc f g h `cast` ()
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `cast` ()

instance Monoid (Endo a) where
  mempty = Endo id
  mconcat = foldrList mappend mempty

instance VMonoid (Endo a) where
  lawEmpty (Endo f) = composeId f
  lawMconcat _ = ()



class Foldable t where
  {-@ foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m @-}
  foldMap :: forall a m. Monoid m => (a -> m) -> t a -> m
  foldr :: (a -> b -> b) -> b -> t a -> b

class Foldable t => VFoldable t where
  {-@ lawFoldable1 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr f z t == appEndo (foldMap (composeEndo f) t ) z} @-}
  lawFoldable1 :: forall a b . (a -> b -> b) -> b -> t a -> ()


instance Foldable Maybe where
  foldMap f Nothing = mempty
  foldMap f (Just x) = f x
  foldr f m Nothing = m
  foldr f m (Just x) = f x m

instance VFoldable Maybe where
  lawFoldable1 _ _ Nothing = ()
  lawFoldable1 _ _ _ = ()

instance Foldable Identity where
  foldMap f (Identity a) = f a
  foldr f m (Identity a) = f a m

instance VFoldable Identity where
  lawFoldable1 _ _ _ = ()


instance Foldable (Const a) where
  foldr f m _ = m
  foldMap _ _ = mempty

instance VFoldable (Const a) where
  lawFoldable1 _ _ _ = ()

data Complex a = Complex a a

instance Foldable Complex where
  foldMap f (Complex a b) = f a `mappend` f b
  foldr f m (Complex a b) = f a (f b m)

instance VFoldable Complex where
  lawFoldable1 _ _ _ = ()

instance Foldable List where
  foldr f z Nil = z
  foldr f z (Cons x xs) = f x (foldr f z xs)
  foldMap f Nil = mempty
  foldMap f (Cons x xs) = f x `mappend` foldMap f xs

instance VFoldable List where
  lawFoldable1 f z Nil  = ()
  lawFoldable1 f z (Cons x xs) = lawFoldable1 f z xs `cast` ()
