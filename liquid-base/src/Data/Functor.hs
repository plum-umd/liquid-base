{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.Functor where

import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , id
                                                )
import           Data.Proxy

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


class (VFunctor f, Applicative f) => VApplicative f where
  {-@ lawApplicativeId :: forall a . v:f a -> {ap (pure id') v = v} @-}
  lawApplicativeId :: f a -> ()

--     TODO: This doesn't type check XXX
--   {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
--   lawApplicativeComposition :: f (b -> c) -> f (a -> b) -> f a -> ()

--   TODO: Cannot elaborate `px`. Add an inline type annotation for VV? XXX
--   {-@ lawApplicativeHomomorphism :: forall a b . g:(a -> b) -> x:a -> {px:f a | px = pure x} -> {ap (pure g) px = pure (g x)} @-}
--   lawApplicativeHomomorphism :: (a -> b) -> a -> f a -> ()

--   TODO: The law doesn't bind `f` and we can't add type annotations to refinement expressions... (old)
--   {-@ lawApplicativeHomomorphism :: forall a b . Proxy (f a) -> g:(a -> b) -> x:a -> {ap (pure g) (pure x :: f a) = pure (g x)} @-}
--   lawApplicativeHomomorphism :: Proxy (f a) -> (a -> b) -> a -> ()



--   TODO: I'm messing this up somehow
--   {-@ lawApplicativeInterchange :: forall a b c . u:f (a -> b -> c) -> y:c -> z:f b -> {ap u (pure y) z = ap (pure (flip apply y)) u z} @-}
--   lawApplicativeInterchange :: f (a -> b -> c) -> c -> f b -> ()



  
{-@ data MyId a = MyId a @-}
data MyId a = MyId a

instance Functor MyId where
  fmap f (MyId i) = MyId (f i)
  x <$ (MyId _) = MyId x

instance VFunctor MyId where
    lawFunctorId = undefined -- TODO: FIXME XXX

  
instance Applicative MyId where
  pure = MyId
  ap (MyId f) (MyId a) = MyId (f a)
  liftA2 f (MyId a) (MyId b) = MyId (f a b)
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 (\x _ -> x) a1 a2

instance VApplicative MyId where
  lawApplicativeId _ = ()

-- TODO: Define `Maybe a` in Data.Maybe
data Optional a = None | Has a

instance Functor Optional where
  fmap _ None = None
  fmap f (Has x) = Has (f x)
  _ <$ None = None
  x <$ (Has _) = Has x

instance VFunctor Optional where
    lawFunctorId = undefined -- TODO: FIXME XXX

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




-- Abstract proofs.

-- -- TODO: Prove this
-- {-@ applicativeLemma1 :: VApplicative m => f:(a -> b) -> x:m a -> {fmap f x = ap (pure f) x} @-}
-- applicativeLemma1 :: VApplicative m => (a -> b) -> m a -> ()
-- applicativeLemma1 f x = undefined
-- 
-- -- TODO: Prove this
-- {-@ applicativeLemma2 :: VApplicative m => f:(d -> c -> e) -> g:(a -> b -> c) -> p:_ -> {q:_ | p (q x y) = compose (f x) (g y)} -> {liftA2 p (liftA2 q u v) = compose (liftA2 f u) (liftA2 g v)} @-}
-- applicativeLemma2 :: VApplicative m => (d -> c -> e) -> (a -> b -> c) -> _ -> _ -> ()
-- applicativeLemma2 f g p q = undefined



