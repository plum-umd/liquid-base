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

--    {-@ lawSconcat :: ys:NonEmpty a -> {foldr mappend (NonEmpty.head' ys) (NonEmpty.tail' ys) == sconcat ys} @-}
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
data PNat = Z | S PNat

instance Semigroup PNat where
  mappend Z     n = n
  mappend (S m) n = S (mappend m n)

  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup PNat where
  lawAssociative Z     _ _ = ()
  lawAssociative (S p) m n = lawAssociative p m n
  lawSconcat (NonEmpty h t) = ()

instance Monoid PNat where
  mempty = Z
  mconcat xs = foldr mappend mempty xs

instance VMonoid PNat where
  lawEmpty Z     = ()
  lawEmpty (S m) = lawEmpty m
  lawMconcat _ = ()


-- Lists

instance Semigroup (List a) where
  mappend Nil l2 = l2
  mappend (Cons h l1) l2 = Cons h (mappend l1 l2)
  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup (List a) where
  lawAssociative Nil y z = ()
  lawAssociative (Cons _ x) y z = lawAssociative x y z
  lawSconcat (NonEmpty h t) = ()

instance Monoid (List a) where
  mempty = Nil
  mconcat xs = foldr mappend mempty xs

instance VMonoid (List a) where
  lawEmpty Nil = ()
  lawEmpty (Cons _ t) = lawEmpty t
  lawMconcat _ = ()


-- -- Dual
{-@ data Dual a = Dual {getDual :: a} @-}
data Dual a = Dual {getDual :: a}


{-@ dualdualHom :: Semigroup a => x:a -> y:a -> {mappend (Dual (Dual x)) (Dual (Dual y)) == Dual (Dual (mappend x y))} @-}
dualdualHom :: Semigroup a => a -> a -> ()
dualdualHom _ _ = ()

{-@ dualdualHom' :: Semigroup a => x:Dual (Dual a) -> y:Dual (Dual a) -> {getDual (getDual (mappend x y)) == mappend (getDual (getDual x)) (getDual (getDual y))} @-}
dualdualHom' :: Semigroup a => Dual (Dual a) -> Dual (Dual a) -> ()
dualdualHom' _ _ = ()

instance Semigroup a => Semigroup (Dual a) where
  mappend (Dual v) (Dual v') = Dual (mappend v' v)
  sconcat (NonEmpty h t) = foldr mappend h t

instance Monoid a => Monoid (Dual a) where
  mempty = Dual mempty
  mconcat xs = foldr mappend mempty xs

instance VSemigroup a => VSemigroup (Dual a) where
  lawAssociative (Dual v) (Dual v') (Dual v'') = lawAssociative v'' v' v
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `P.cast` ()

instance VMonoid a => VMonoid (Dual a) where
  lawEmpty (Dual v) = lawEmpty v
  lawMconcat xs = mconcat xs `P.cast` ()

{-@ data Endo a = Endo {appEndo :: a -> a} @-}
data Endo a = Endo {appEndo :: a -> a}

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

{-@ reflect id' @-}
id' :: a -> a
id' x = x

instance Semigroup (Endo a) where
  mappend (Endo f) (Endo g) = Endo (compose f g)
  sconcat (NonEmpty h t) = foldr mappend h t


{-@ assume axiomExt :: f:_ -> g:_ -> (x:_ -> {f x == g x}) -> {f = g} @-}
axiomExt :: (a -> b) -> (a -> b) -> (a -> ()) -> ()
axiomExt _ _ _ = () 


{-@ composeAssoc :: f:(c -> d) -> g:(b -> c) -> h:(a -> b) -> { compose f (compose g h) == compose (compose f g) h  } @-}
composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> ()
composeAssoc f g h = axiomExt (compose (compose f g) h) (compose f (compose g h)) $ \a ->
  compose (compose f g) h a `P.cast`
  f (g (h a)) `P.cast`
  compose f (compose g h) a `P.cast`
  ()

{-@ composeId :: f:(a -> b) -> {compose id' f == f && compose f id' == f} @-}
composeId :: (a -> b) -> ()
composeId f = (axiomExt (compose id' f) f $ \x -> compose id' f x `P.cast` ()) `P.cast`
              (axiomExt (compose f id') f $ \x -> compose f id' x `P.cast` ())

instance VSemigroup (Endo a) where
  lawAssociative (Endo f) (Endo g) (Endo h) = composeAssoc f g h `P.cast` ()
  lawSconcat (NonEmpty h t) = sconcat (NonEmpty h t) `P.cast` ()

instance Monoid (Endo a) where
  mempty = Endo id'
  mconcat = foldr mappend mempty

instance VMonoid (Endo a) where
  lawEmpty (Endo f) = composeId f
  lawMconcat _ = ()


data Any = Any {getAny :: Bool}
data All = All {getAll :: Bool}

instance Semigroup Any where --
  mappend (Any b) (Any b') = Any $ b || b'
  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup Any where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid Any where
  mempty = Any False
  mconcat = foldr mappend mempty

instance VMonoid Any where
  lawMconcat _ = ()
  lawEmpty _ = ()

instance Semigroup All where
  mappend (All b) (All b') = All $ b && b'
  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup All where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid All where
  mempty = All True
  mconcat = foldr mappend mempty

instance VMonoid All where
  lawMconcat _ = ()
  lawEmpty _ = ()

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

{-@ data Maybe a = Nothing | Just a @-}
data Maybe a = Nothing | Just a

data First a = First {getFirst :: Maybe a}

instance Semigroup (First a) where
  First Nothing `mappend` b = b
  a `mappend` _ = a
  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup (First a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid (First a) where
  mempty = First Nothing
  mconcat = foldr mappend mempty

instance VMonoid (First a) where
  lawEmpty (First Nothing) = ()
  lawEmpty _ = ()
  lawMconcat _ = ()

data Last a = Last {getLast :: Maybe a}

instance Semigroup (Last a) where
  a `mappend` Last Nothing = a
  _ `mappend` b = b
  sconcat (NonEmpty h t) = foldr mappend h t

instance VSemigroup (Last a) where
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance Monoid (Last a) where
  mempty = Last Nothing
  mconcat = foldr mappend mempty

instance VMonoid (Last a) where
  lawEmpty (Last Nothing) = ()
  lawEmpty _ = ()
  lawMconcat _ = ()

-- -- Dual First and Last are isomorphic
instance Semigroup a => Semigroup (Maybe a) where
  Nothing `mappend` b = b
  a `mappend` Nothing = a
  Just a `mappend` Just b = Just (a `mappend` b)
  sconcat (NonEmpty h t) = foldr mappend h t
  
  
instance Semigroup a => Monoid (Maybe a) where
  mempty = Nothing
  mconcat = foldr mappend mempty

instance VSemigroup a => VSemigroup (Maybe a) where
  lawAssociative (Just x) (Just y) (Just z) = lawAssociative x y z
  lawAssociative _ _ _ = ()
  lawSconcat _ = ()

instance VMonoid a => VMonoid (Maybe a) where
  lawMconcat xs = mconcat xs `P.cast` ()
  lawEmpty Nothing = ()
  lawEmpty (Just x) = lawEmpty x

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

class Foldable t => VFoldable t where
  {-@ lawFoldable1 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr f z t == appEndo (foldMap (composeEndo f) t ) z} @-}
  lawFoldable1 :: forall a b . (a -> b -> b) -> b -> t a -> ()
--  {-@ lawFoldable2 :: forall a b. f:(b -> a -> b) -> z:b -> t:t a -> {foldl f z t = appEndo (getDual (foldMap (dualEndoFlip f) t)) z} @-}
--  lawFoldable2 :: forall a b. (b -> a -> b) -> b -> t a -> ()
--  {-@ lawFoldable3 :: forall a b. f:(a -> b -> b) -> z:b -> t:t a -> {foldr' f z t = foldMap id' f z t} @-}
--  lawFoldable3 :: forall a b . (a -> b -> b) -> b -> t a -> ()

data Id a = Id a

instance Foldable Maybe where
  foldMap f Nothing = mempty
  foldMap f (Just x) = f x
  foldr f m Nothing = m
  foldr f m (Just x) = f x m
  -- foldl f m Nothing = m
  -- foldl f m (Just x) = f m x

instance VFoldable Maybe where
  lawFoldable1 _ _ Nothing = ()
  lawFoldable1 _ _ _ = ()
  -- lawFoldable2 _ _ Nothing = ()
  -- lawFoldable2 _ _ _ = ()

instance Foldable Id where
  foldMap f (Id a) = f a
  foldr f m (Id a) = f a m

instance VFoldable Id where
  lawFoldable1 _ _ _ = ()

data Const a b = Const {getConst :: a}

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
  lawFoldable1 f z (Cons x xs) = lawFoldable1 f z xs `P.cast` ()




  -- foldl f z Nil = z
  -- foldl f z (Cons x xs) = foldl f (f z x) xs


