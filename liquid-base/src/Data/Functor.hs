{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Functor where

import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , id
                                                )

{-@ reflect id' @-}
id' :: a -> a
id' x = x

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose g f x = g (f x)

class Functor f where
  {-@ fmap :: forall a b. (a -> b) -> f a -> f b @-}
  fmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a

class Functor m => VFunctor m where
    {-@ lawFunctorId :: forall a . x:m a -> {fmap id' x == id' x} @-}
    lawFunctorId :: m a -> ()

--     TODO: This doesn't unify XXX
--     {-@ lawFunctorComposition :: forall a b c . f:(b -> c) -> g:(a -> b) -> x:m a -> { fmap (compose f g) x == compose (fmap f) (fmap g) x } @-}
--     lawFunctorComposition :: (b -> c) -> (a -> b) -> m a -> ()

class Functor f => Applicative f where
  {-@ pure :: forall a. a -> f a @-}
  pure :: a -> f a
  {-@ ap :: forall a b. f (a -> b) -> f a -> f b @-}
  ap :: f (a -> b) -> f a -> f b
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  (*>) :: f a -> f b -> f b
  (<*) :: f a -> f b -> f a


class (Functor f, Applicative f) => VApplicative f where
  {-@ lawApplicativeId :: forall a . v:f a -> {ap (pure id') v = v} @-}
  lawApplicativeId :: f a -> ()
  {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
  lawApplicativeComposition :: f (b -> c) -> f (a -> b) -> f a -> ()

  -- {-@ myprop :: forall a b . x:f a -> f:(a -> b) -> {fmap f x == ap (pure f) x} @-}
  -- myprop :: f a -> (a -> b) -> ()

  
{-@ data MyId a = MyId a @-}
data MyId a = MyId a

instance Functor MyId where
  fmap f (MyId i) = MyId (f i)
  x <$ (MyId _) = MyId x
  
instance Applicative MyId where
  pure = MyId
  ap (MyId f) (MyId a) = MyId (f a)
  liftA2 f (MyId a) (MyId b) = MyId (f a b)
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 (\x _ -> x) a1 a2

instance VApplicative MyId where
  lawApplicativeId _ = ()

  -- myprop _ _ = ()

-- TODO: Define `Maybe a` in Data.Maybe
data Optional a = None | Has a

instance Functor Optional where
  fmap _ None = None
  fmap f (Has x) = Has (f x)
  _ <$ None = None
  x <$ (Has _) = Has x

instance Applicative Optional where
  pure = Has
  ap None _ = None
  ap _ None = None
  ap (Has f) (Has x) = Has (f x)
  liftA2 f (Has a) (Has b) = Has (f a b)
  liftA2 f _       _       = None
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 (\x _ -> x) a1 a2

instance VApplicative Optional where
  lawApplicativeId _ = undefined -- TODO: FIXME XXX

  -- myprop _ _ = ()

{-@ impl :: x:Bool -> y:Bool -> {v:Bool | v <=> (x => y)} @-}
impl :: Bool -> Bool -> Bool
impl a b = if a then b else True

{-@ reflect ffmap @-}
ffmap :: Functor f => (a -> b) -> f a -> f b
ffmap = fmap

{-@ trivial :: Functor f => f:(a -> b) -> x:f a -> {fmap f x == ffmap f x} @-}
trivial :: Functor f => (a -> b) -> f a -> ()
trivial _ _ = ()
