{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)
                                                )

class Semigroup a where
    mappend :: a -> a -> a
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {mappend (mappend v v') v'' == mappend v (mappend v' v'')} @-}
    lawAssociative :: a -> a -> a -> ()


class Semigroup a => Monoid a where
   mempty :: a
   {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
   lawEmpty :: a -> ()


-- Natural Numbers
data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n

instance Monoid PNat where
  mempty = Z
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m
