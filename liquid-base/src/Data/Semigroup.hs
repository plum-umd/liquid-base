{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Semigroup where

import           Prelude                 hiding ( Semigroup(..)
                                                , Monoid(..)

                                                )

data VList a = VNil | VCons a (VList a)

class Semigroup a where
    mappend :: a -> a -> a

class Semigroup a => VSemigroup a where
    {-@ lawAssociative :: v:a -> v':a -> v'':a -> {mappend (mappend v v') v'' == mappend v (mappend v' v'')} @-}
    sconcat :: a -> VList a -> a
    lawAssociative :: a -> a -> a -> ()
    {-@ lawSconcat :: x:a -> ys:VList a -> {vfoldr mappend x ys == sconcat x ys} @-}
    lawSconcat :: a -> VList a -> ()

class Semigroup a => Monoid a where
    mempty :: a

class (VSemigroup a, Monoid a) => VMonoid a where
    {-@ lawEmpty :: x:a -> {mappend x mempty == x && mappend mempty x == x} @-}
    lawEmpty :: a -> ()


{-@ reflect vfoldr @-}
vfoldr :: (a -> b -> b) -> b -> VList a -> b
vfoldr _ x VNil = x
vfoldr f x (VCons y ys) = vfoldr f (f y x) ys

-- Natural Numbers
data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)

instance VSemigroup PNat where
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n
  sconcat = vfoldr mappend
  lawSconcat _ _ = ()

instance Monoid PNat where
  mempty = Z

instance VMonoid PNat where
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m

