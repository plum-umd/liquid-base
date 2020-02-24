{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
module Data.Functor where

import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , id
                                                )
import           Data.Proxy
import           Liquid.ProofCombinators

-- TODO: Move these to a separate module. 
{-@ reflect id' @-}
id' :: a -> a
id' x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose g f x = g (f x)

{-@ reflect apply @-}
apply :: (a -> b) -> a -> b
apply f x = f x

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b

{-@ reflect const' @-}
const' :: a -> b -> a
const' x _ = x

class Functor f where
  {-@ fmap :: forall a b. (a -> b) -> f a -> f b @-}
  fmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a

class Functor m => VFunctor m where
    {-@ lawFunctorId :: forall a . x:m a -> {fmap id' x == id' x} @-}
    lawFunctorId :: m a -> ()

    {-@ lawFunctorComposition :: forall a b c . f:(b -> c) -> g:(a -> b) -> x:m a -> { fmap (compose f g) x == compose (fmap f) (fmap g) x } @-}
    lawFunctorComposition :: forall a b c. (b -> c) -> (a -> b) -> m a -> ()

class Functor f => Applicative f where
  {-@ pure :: forall a. a -> f a @-}
  pure :: a -> f a
  {-@ ap :: forall a b. f (a -> b) -> f a -> f b @-}
  ap :: f (a -> b) -> f a -> f b
  {-@ liftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c @-}
  liftA2 :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
  (*>) :: f a -> f b -> f b
  (<*) :: f a -> f b -> f a


class (VFunctor f, Applicative f) => VApplicative f where
  {-@ lawApplicativeId :: forall a . v:f a -> {ap (pure id') v = v} @-}
  lawApplicativeId :: f a -> ()

  {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
  lawApplicativeComposition :: forall a b c. f (b -> c) -> f (a -> b) -> f a -> ()

  {-@ lawApplicativeHomomorphism :: forall a b . g:(a -> b) -> x:a -> {px:f a | px = pure x} -> {ap (pure g) px = pure (g x)} @-}
  lawApplicativeHomomorphism :: forall a b. (a -> b) -> a -> f a -> ()

  {-@ lawApplicativeInterchange :: forall a b . u:f (a -> b) -> y:a -> {ap u (pure y) = ap (pure (flip apply y)) u} @-}
  lawApplicativeInterchange :: forall a b . f (a -> b) -> a -> ()

  
{-@ data MyId a = MyId a @-}
data MyId a = MyId a

instance Functor MyId where
  fmap f (MyId i) = MyId (f i)
  x <$ (MyId _) = MyId x

instance VFunctor MyId where
    lawFunctorId _ = ()
    lawFunctorComposition f g (MyId x) = ()

  
instance Applicative MyId where
  pure = MyId
  ap (MyId f) (MyId a) = MyId (f a)
  liftA2 f (MyId a) (MyId b) = MyId (f a b)
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

instance VApplicative MyId where
  lawApplicativeId _ = ()
  lawApplicativeComposition (MyId f) (MyId g) (MyId x) = ()
  lawApplicativeHomomorphism f x (MyId y) = ()
  lawApplicativeInterchange (MyId f) _ = ()


-- TODO: Define `Maybe a` in Data.Maybe
data Optional a = None | Has a

instance Functor Optional where
  fmap _ None = None
  fmap f (Has x) = Has (f x)
  _ <$ None = None
  x <$ (Has _) = Has x

instance VFunctor Optional where
    lawFunctorId x = ()
    lawFunctorComposition f g None = ()
    lawFunctorComposition f g (Has x) = ()

instance Applicative Optional where
  pure = Has
  ap None _ = None
  ap _ None = None
  ap (Has f) (Has x) = Has (f x)
  liftA2 f (Has a) (Has b) = Has (f a b)
  liftA2 f _       _       = None
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

instance VApplicative Optional where
  lawApplicativeId None = ()
  lawApplicativeId (Has x) = ap (pure id') (Has x) `cast` ()
  lawApplicativeComposition (Has f) (Has g) (Has x) = ()
  lawApplicativeComposition _ _ _ = ()
  lawApplicativeHomomorphism f x (Has y) = ()
  lawApplicativeHomomorphism f x None = ()
  lawApplicativeInterchange None _ = ()
  lawApplicativeInterchange (Has f) _ = ()




-- Abstract proofs.

-- -- TODO: Prove this
-- {-@ applicativeLemma1 :: VApplicative m => f:(a -> b) -> x:m a -> {fmap f x == ap (pure f) x} @-}
-- applicativeLemma1 :: VApplicative m => (a -> b) -> m a -> ()
-- applicativeLemma1 f x = ()

-- -- TODO: Prove this
-- {-@ applicativeLemma2 :: VApplicative m => f:(d -> c -> e) -> g:(a -> b -> c) -> p:_ -> {q:_ | p (q x y) = compose (f x) (g y)} -> {liftA2 p (liftA2 q u v) = compose (liftA2 f u) (liftA2 g v)} @-}
-- applicativeLemma2 :: VApplicative m => (d -> c -> e) -> (a -> b -> c) -> _ -> _ -> ()
-- applicativeLemma2 f g p q = undefined



