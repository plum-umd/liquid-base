{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                , foldr
                                                , head
                                                , tail
                                                )

import           Data.List
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NonEmpty
import qualified Liquid.ProofCombinators

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

class (VSemigroup a, Monoid a) => VMonoid a where
    {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
    lawEmpty :: a -> ()


-- Natural Numbers
data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)

  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup PNat where
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n
  lawSconcat _ = ()

instance Monoid PNat where
  mempty = Z

instance VMonoid PNat where
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m

-- Dual
data Dual a = Dual {getDual :: a}

instance Semigroup a => Semigroup (Dual a) where
  mappend (Dual v) (Dual v') = Dual (mappend v' v)
  sconcat (NonEmpty h t) = foldr mappend h t

instance Monoid a => Monoid (Dual a) where
  mempty = Dual mempty

instance VSemigroup a => VSemigroup (Dual a) where
  lawAssociative (Dual v) (Dual v') (Dual v'') = lawAssociative v'' v' v
  lawSconcat _ = ()

-- instance VMonoid a => VMonoid (Dual a) where
--   lawEmpty (Dual v) = lawEmpty v
