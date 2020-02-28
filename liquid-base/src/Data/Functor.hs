{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
module Data.Functor where

import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , Monad(..)
                                                , id
                                                )
import           Data.Proxy
import           Liquid.ProofCombinators
import           Data.List

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

  
{-@ data Id a = Id a @-}
data Id a = Id a

instance Functor Id where
  fmap f (Id i) = Id (f i)
  x <$ (Id _) = Id x

instance VFunctor Id where
    lawFunctorId _ = ()
    lawFunctorComposition f g (Id x) = ()

  
instance Applicative Id where
  pure = Id
  ap (Id f) (Id a) = Id (f a)
  liftA2 f (Id a) (Id b) = Id (f a b)
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

instance VApplicative Id where
  lawApplicativeId _ = ()
  lawApplicativeComposition (Id f) (Id g) (Id x) = ()
  lawApplicativeHomomorphism f x (Id y) = ()
  lawApplicativeInterchange (Id f) _ = ()


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

class Applicative m => Monad m where
  {-@ bind :: forall a b. m a -> (a -> m b) -> m b @-}
  bind :: forall a b. m a -> (a -> m b) -> m b
  return :: forall a. a -> m a
  mseq :: forall a b. m a -> m b -> m b

class (VApplicative m, Monad m) => VMonad m where
  {-@ lawMonad1 :: forall a b. x:a -> f:(a -> m b) -> {f x == bind (return x) f} @-}
  lawMonad1 :: forall a b. a -> (a -> m b) -> ()
  {-@ lawMonad2 :: forall a. m:m a -> {bind m return == m }@-}
  lawMonad2 :: forall a. m a -> ()
  {-@ lawMonad3 :: forall a b c. m:m a -> f:(a -> m b) -> g:(b -> m c) -> {h:(y:a -> {v0:m c | v0 = bind (f y) g}) | True} -> {bind (bind m f) g == bind m h} @-}
  lawMonad3 :: forall a b c. m a -> (a -> m b) -> (b -> m c) -> (a -> m c) -> ()
  -- iff is buggy
  {-@ lawMonadReturn :: forall a. x:a -> y:m a -> {((y == pure x) => (y == return x)) && ((y == return x) => (y == pure x)) } @-}
  lawMonadReturn :: forall a. a -> m a -> ()
  

instance Monad Id where
  bind (Id x) f = f x
  return = Id
  mseq  _ x = x

instance VMonad Id where
  lawMonad1 x f = ()
  lawMonad2 (Id x) = ()
  lawMonad3 (Id x) f g h = h x `cast` ()
  lawMonadReturn _ _ = ()


instance Monad Optional where
  bind None _ = None
  bind (Has x) f = f x
  return = Has
  mseq _ (Has x) = Has x
  mseq _ None = None

instance VMonad Optional where
  lawMonad1 x f = ()
  lawMonad2 None = ()
  lawMonad2 (Has x) = ()
  lawMonad3 None f g h = ()
  lawMonad3 (Has x) f g h = h x `cast` ()
  lawMonadReturn _ _ = ()

{-@ data State s a = State {runState :: s -> (a,s)} @-}
data State s a = State {runState :: s -> (a,s)}


{-@ reflect fmapState @-}
fmapState :: (a -> b) -> (s -> (a,s)) -> s -> (b,s)
fmapState f h s = let (a,s') = h s in (f a, s')


{-@ fmapStateId' :: f:(s -> (a,s)) -> {fmapState id' f == id' f}  @-}
fmapStateId' :: (s -> (a,s)) -> ()
fmapStateId' f = axiomExt (fmapState id' f) (id' f) $ \s ->
  let (a,s') = f s 
      (a',s'') = fmapState id' f s in
    id' a `cast` id' a' `cast` ()
  
{-@ lawFunctorCompositionState :: f:(b -> c) -> g:(a -> b) -> x:(s -> (a,s)) -> {fmapState (compose f g) x == compose (fmapState f) (fmapState g) x} @-}
lawFunctorCompositionState :: (b -> c) -> (a -> b) -> (s -> (a, s)) -> ()
lawFunctorCompositionState f g x =
  axiomExt (fmapState (compose f g) x) (compose (fmapState f) (fmapState g) x) $ \s ->
    let (c, s') = fmapState (compose f g) x s
        (c', s'') = compose (fmapState f) (fmapState g) x s
        (a, s''') = x s
    in ()


      
    

{-@ assume axiomExt :: f:_ -> g:_ -> (x:_ -> {f x == g x}) -> {f = g} @-}
axiomExt :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
axiomExt _ _ _ = () 

instance Functor (State s) where
  fmap f (State g) = State (fmapState f g)
  a <$ (State f) =
    State $ \s ->
      let (_, s') = f s
       in (a, s')

instance VFunctor (State s) where
  lawFunctorId (State f) = fmapStateId' f `cast` ()
  -- TODO: composition law could be messy
  lawFunctorComposition f g (State h) = lawFunctorCompositionState f g h `cast` ()


instance Functor List where
  fmap _ Nil = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)
  y <$ Nil = Nil
  y <$ (Cons x xs) = Cons y (y <$ xs)

instance VFunctor List where  
  lawFunctorId Nil = ()
  lawFunctorId (Cons _ xs) = lawFunctorId xs
  lawFunctorComposition _ _ Nil = ()
  lawFunctorComposition f g (Cons _ xs) = lawFunctorComposition f g xs

{-@ reflect appendL @-}
appendL :: List a -> List a -> List a
appendL Nil ys = Nil
appendL (Cons x xs) ys = Cons x (appendL xs ys)


instance Applicative List where
  pure x = Cons x Nil
  ap Nil _ = Nil
  ap (Cons f fs) xs = fmap f xs `appendL` ap fs xs
  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

instance VApplicative List where
  lawApplicativeId Nil = ()
  lawApplicativeId (Cons x xs) = lawApplicativeId xs
  lawApplicativeComposition Nil (Cons g gs) (Cons x xs) = ()
  -- finishing up
  lawApplicativeComposition (Cons f fs) (Cons g gs) (Cons x xs) = undefined
    
  lawApplicativeComposition _ _ _ = undefined
  lawApplicativeHomomorphism f x Nil = ()
  lawApplicativeHomomorphism f x (Cons y ys) = undefined
  lawApplicativeInterchange Nil _ = ()
  lawApplicativeInterchange (Cons y ys) _ = undefined

-- Kleisli Arrow
{-@ reflect kcompose @-}
kcompose :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
kcompose f g x = bind (f x) g

-- {-@ kcomposeAssoc :: Monad m => f:(a -> m b) -> g:(b -> m c) -> h:(c -> m d) -> x:a -> {kcompose (kcompose f g) h x == kcompose f (kcompose g h) x} @-}
-- kcomposeAssoc :: VMonad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> ()
-- kcomposeAssoc f g h x = lawMonad3  (f x) g h (kcompose g h)

-- Instantiation
-- {-@ optionCompose :: f:(a -> Optional b) -> g:(b -> Optional c) -> h:(c -> Optional d) -> x:a -> {kcompose (kcompose f g) h x == kcompose f (kcompose g h) x} @-}
-- optionCompose :: (a -> Optional b) -> (b -> Optional c) -> (c -> Optional d) -> a -> ()
-- optionCompose  = kcomposeAssoc 


-- -- TODO: Prove this
-- {-@ applicativeLemma1 :: VApplicative m => f:(a -> b) -> x:m a -> {fmap f x == ap (pure f) x} @-}
-- applicativeLemma1 :: VApplicative m => (a -> b) -> m a -> ()
-- applicativeLemma1 f x = ()

-- -- TODO: Prove this
-- {-@ applicativeLemma2 :: VApplicative m => f:(d -> c -> e) -> g:(a -> b -> c) -> p:_ -> {q:_ | p (q x y) = compose (f x) (g y)} -> {liftA2 p (liftA2 q u v) = compose (liftA2 f u) (liftA2 g v)} @-}
-- applicativeLemma2 :: VApplicative m => (d -> c -> e) -> (a -> b -> c) -> _ -> _ -> ()
-- applicativeLemma2 f g p q = undefined



