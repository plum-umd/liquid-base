{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Functor where

import           Prelude                 hiding ( Functor(..)
                                                , Applicative(..)
                                                , Monad(..)
                                                , Foldable(..)
                                                , Maybe(..)
                                                , Monoid(..)
                                                , Semigroup(..)
                                                , Either(..)
                                                , id
                                                , flip
                                                )
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


{-@ data Id a = Id a @-}
data Id a = Id a

-- instance Functor Id where
--   fmap f (Id i) = Id (f i)
--   x <$ (Id _) = Id x

-- instance VFunctor Id where
--     lawFunctorId _ = ()
--     lawFunctorComposition f g (Id x) = ()


-- instance Applicative Id where
--   pure = Id
--   ap (Id f) (Id a) = Id (f a)
--   liftA2 f (Id a) (Id b) = Id (f a b)
--   a1 *> a2 = ap (id' <$ a1) a2
--   a1 <* a2 = liftA2 const' a1 a2

-- instance VApplicative Id where
--   lawApplicativeId _ = ()
--   lawApplicativeComposition (Id f) (Id g) (Id x) = ()
--   lawApplicativeHomomorphism f x (Id y) = ()
--   lawApplicativeInterchange (Id f) _ = ()


-- TODO: Define `Maybe a` in Data.Maybe
data Maybe a = Nothing | Just a

-- instance Functor Maybe where
--   fmap _ Nothing = Nothing
--   fmap f (Just x) = Just (f x)
--   _ <$ Nothing = Nothing
--   x <$ (Just _) = Just x

-- instance VFunctor Maybe where
--     lawFunctorId x = ()
--     lawFunctorComposition f g Nothing = ()
--     lawFunctorComposition f g (Just x) = ()

-- instance Applicative Maybe where
--   pure = Just
--   ap Nothing _ = Nothing
--   ap _ Nothing = Nothing
--   ap (Just f) (Just x) = Just (f x)
--   liftA2 f (Just a) (Just b) = Just (f a b)
--   liftA2 f _       _       = Nothing
--   a1 *> a2 = ap (id' <$ a1) a2
--   a1 <* a2 = liftA2 const' a1 a2

-- instance VApplicative Maybe where
--   lawApplicativeId Nothing = ()
--   lawApplicativeId (Just x) = ap (pure id') (Just x) `cast` ()
--   lawApplicativeComposition (Just f) (Just g) (Just x) = ()
--   lawApplicativeComposition _ _ _ = ()
--   lawApplicativeHomomorphism f x (Just y) = ()
--   lawApplicativeHomomorphism f x Nothing = ()
--   lawApplicativeInterchange Nothing _ = ()
--   lawApplicativeInterchange (Just f) _ = ()


-- instance Monad Maybe where
--   bind Nothing _ = Nothing
--   bind (Just x) f = f x
--   return = Just
--   mseq _ (Just x) = Just x
--   mseq _ Nothing = Nothing

-- instance VMonad Maybe where
--   lawMonad1 x f = ()
--   lawMonad2 Nothing = ()
--   lawMonad2 (Just x) = ()
--   lawMonad3 Nothing f g h = ()
--   lawMonad3 (Just x) f g h = h x `cast` ()
--   lawMonadReturn _ _ = ()



-- instance Monad Id where
--   bind (Id x) f = f x
--   return = Id
--   mseq  _ x = x

-- instance VMonad Id where
--   lawMonad1 x f = ()
--   lawMonad2 (Id x) = ()
--   lawMonad3 (Id x) f g h = h x `cast` ()
--   lawMonadReturn _ _ = ()



-- {-@ data State s a = State {runState :: s -> (a,s)} @-}
-- data State s a = State {runState :: s -> (a,s)}


-- {-@ reflect fmapState @-}
-- fmapState :: (a -> b) -> (s -> (a, s)) -> s -> (b, s)
-- fmapState f h s = let (a, s') = h s in (f a, s')


-- {-@ fmapStateId' :: f:(s -> (a,s)) -> {fmapState id' f == id' f}  @-}
-- fmapStateId' :: (s -> (a, s)) -> ()
-- fmapStateId' f = axiomExt (fmapState id' f) (id' f) $ \s ->
--   let (a , s' ) = f s
--       (a', s'') = fmapState id' f s
--   in  id' a `cast` id' a' `cast` ()

-- {-@ lawFunctorCompositionState :: f:(b -> c) -> g:(a -> b) -> x:(s -> (a,s)) -> {fmapState (compose f g) x == compose (fmapState f) (fmapState g) x} @-}
-- lawFunctorCompositionState :: (b -> c) -> (a -> b) -> (s -> (a, s)) -> ()
-- lawFunctorCompositionState f g x =
--   axiomExt (fmapState (compose f g) x) (compose (fmapState f) (fmapState g) x)
--     $ \s ->
--         let (c , s'  ) = fmapState (compose f g) x s
--             (c', s'' ) = compose (fmapState f) (fmapState g) x s
--             (a , s''') = x s
--         in  ()

{-@ assume axiomExt :: f:_ -> g:_ -> (x:_ -> {f x == g x}) -> {f = g} @-}
axiomExt :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof
axiomExt _ _ _ = ()

-- instance Functor (State s) where
--   fmap f (State g) = State (fmapState f g)
--   a <$ (State f) = State $ \s -> let (_, s') = f s in (a, s')

-- instance VFunctor (State s) where
--   lawFunctorId (State f) = fmapStateId' f `cast` ()
--   lawFunctorComposition f g (State h) =
--     lawFunctorCompositionState f g h `cast` ()


instance Functor List where
  fmap _ Nil         = Nil
  fmap f (Cons x xs) = Cons (f x) (fmap f xs)
  y <$ Nil         = Nil
  y <$ (Cons x xs) = Cons y (y <$ xs)

instance VFunctor List where
  lawFunctorId Nil         = ()
  lawFunctorId (Cons _ xs) = lawFunctorId xs
  lawFunctorComposition _ _ Nil         = ()
  lawFunctorComposition f g (Cons _ xs) = lawFunctorComposition f g xs

{-@ reflect appendL @-}
appendL :: List a -> List a -> List a
appendL Nil         ys = ys
appendL (Cons x xs) ys = Cons x (appendL xs ys)

{-@ appendLNil :: xs:List a -> {appendL xs Nil == xs} @-}
appendLNil :: List a -> ()
appendLNil Nil         = ()
appendLNil (Cons x xs) = appendLNil xs

{-@ appendLAssoc :: xs:List a -> ys:List a -> zs:List a -> {appendL (appendL xs ys) zs == appendL xs (appendL ys zs)} @-}
appendLAssoc :: List a -> List a -> List a -> ()
appendLAssoc Nil         _  _  = ()
appendLAssoc (Cons _ xs) ys zs = appendLAssoc xs ys zs

instance Applicative List where
  pure x = Cons x Nil
  ap Nil         _  = Nil
  ap (Cons f fs) xs = fmap f xs `appendL` ap fs xs
  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

{-@ apDistrib :: f:List (a -> b) -> g:List (a -> b) -> xs:List a -> {ap (appendL f g) xs == appendL (ap f xs) (ap g xs)}  @-}
apDistrib :: List (a -> b) -> List (a -> b) -> List a -> ()
apDistrib Nil _ _ = ()
apDistrib fs@(Cons f fs') gs xs =
  apDistrib fs' gs xs `cast` appendLAssoc (fmap f xs) (ap fs' xs) (ap gs xs)

{-@ fmapResAppend :: f:(a -> b) -> xs:List a -> ys:List a -> {fmap f (appendL xs ys) == appendL (fmap f xs) (fmap f ys)} @-}
fmapResAppend :: (a -> b) -> List a -> List a -> ()
fmapResAppend f Nil         ys = ()
fmapResAppend f (Cons _ xs) ys = fmapResAppend f xs ys

--  {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
{-@ lawfListList :: f:(b -> c) -> gs: List (a -> b) -> as:List a -> {fmap f (ap gs as) == ap (fmap (compose f) gs) as } @-}
lawfListList :: (b -> c) -> List (a -> b) -> List a -> ()
lawfListList f Nil xs = ()
lawfListList f (Cons g gs) xs =
  fmapResAppend f (fmap g xs) (ap gs xs)
    `cast` lawfListList f gs xs
    `cast` lawFunctorComposition f g xs

instance VApplicative List where
  lawApplicativeId Nil         = ()
  lawApplicativeId (Cons x xs) = lawApplicativeId xs

  lawApplicativeComposition Nil (Cons g gs) (Cons x xs) = ()
  lawApplicativeComposition (Cons f fs) v w =
    appendLNil (fmap compose (Cons f fs))
      `cast` apDistrib (fmap (compose f) v) (ap (fmap compose fs) v) w
      `cast` lawApplicativeComposition fs v w
      `cast` lawfListList f v w
      `cast` ()

  lawApplicativeComposition _ _ _ = ()
  lawApplicativeHomomorphism f x _ = appendLNil (fmap f (Cons x Nil))
  lawApplicativeInterchange Nil _ = ()
  lawApplicativeInterchange (Cons u us) y =
    lawApplicativeInterchange us y
      `cast` appendLNil (fmap (flip apply y) us)
      `cast` appendLNil (fmap (flip apply y) (Cons u us))
      `cast` ()

instance Monad List where
  bind Nil         f = Nil
  bind (Cons x xs) f = f x `appendL` bind xs f
  return = pure
  mseq Nil         _  = Nil
  mseq (Cons _ xs) ys = ys `appendL` mseq xs ys

{-@ listBindDistrib :: xs:List a -> ys:List a -> f:(a -> List b) -> {appendL (bind xs f) (bind ys f) == bind (appendL xs ys) f} @-}
listBindDistrib :: List a -> List a -> (a -> List b) -> ()
listBindDistrib (Cons x xs) ys f =
  appendLAssoc (f x) (bind xs f) (bind ys f) `cast` listBindDistrib xs ys f
listBindDistrib _ _ _ = ()

instance VMonad List where
  lawMonad1 x f = appendLNil (f x)
  lawMonad2 Nil         = ()
  lawMonad2 (Cons _ xs) = lawMonad2 xs
  lawMonad3 Nil f g h = ()
  lawMonad3 (Cons x xs) f g h =
    listBindDistrib (f x) (bind xs f) g
      `cast` lawMonad3 xs f g h
      `cast` h x
      `cast` ()
  lawMonadReturn _ _ = ()


-- This is the last one
data Succs a = Succs a (List a)

instance Functor Succs where
  fmap f (Succs o s) = Succs (f o) (fmap f s)
  y <$ (Succs _ s) = Succs y  (y <$ s)

instance VFunctor Succs where
  lawFunctorId (Succs _ xs) = lawFunctorId xs
  lawFunctorComposition f g (Succs _ xs)    = lawFunctorComposition f g  xs

instance Applicative Succs where
  pure x = Succs x Nil
  -- fmap (flip apply x) fs == ap fs (pure x)
  -- Succs (f x) (ap fs (pure x) `appendL` fmap f xs)
  ap (Succs f fs) (Succs x xs) = Succs (f x) (fmap (flip apply x) fs `appendL` fmap f xs)
  -- ap (Succs f fs) (Succs x xs) = Succs (f x) (fmap (flip apply x) fs `appendL` fmap f xs)
  -- ap Nil         _  = Nil
  -- ap (Cons f fs) xs = fmap f xs `appendL` ap fs xs

  liftA2 f x y = pure f `ap` x `ap` y
  a1 *> a2 = ap (id' <$ a1) a2
  a1 <* a2 = liftA2 const' a1 a2

--  {-@ lawApplicativeId :: forall a . v:f a -> {ap (pure id') v = v} @-}
--  {-@ lawApplicativeComposition :: forall a b c . u:f (b -> c) -> v:f (a -> b) -> w:f a -> {ap (ap (ap (pure compose) u) v) w = ap u (ap v w)} @-}
--  {-@ lawApplicativeHomomorphism :: forall a b . g:(a -> b) -> x:a -> {px:f a | px = pure x} -> {ap (pure g) px = pure (g x)} @-}
--  {-@ lawApplicativeInterchange :: forall a b . u:f (a -> b) -> y:a -> {ap u (pure y) = ap (pure (flip apply y)) u} @-}

{-@ fmapFGEq :: f:(a -> b) -> g:(a -> b) -> xs:List a -> (x:a -> {f x == g x}) -> {fmap f xs == fmap g xs} @-}
fmapFGEq :: (a -> b) -> (a -> b) -> List a -> (a -> ()) -> ()
fmapFGEq f g Nil h = ()
fmapFGEq f g (Cons x xs) h = h x `cast` fmapFGEq f g xs h


{-@ trivialEq0 :: x:a -> g:(a -> b) -> f:(b -> c) -> {compose (flip apply x) (compose (flip apply g) compose) f == flip apply (g x) f} @-}
trivialEq0 :: a -> (a -> b) -> (b -> c) -> ()
trivialEq0 _ _ _ = ()

{-@ trivialEq1 :: x:a -> f:(b -> c) -> g:(a -> b) -> {compose (flip apply x) (compose f) g == compose f (flip apply x) g} @-}
trivialEq1 :: a -> (b -> c) -> (a -> b) -> ()
trivialEq1 _ _ _ =()

instance VApplicative Succs where
  lawApplicativeId (Succs x xs)  = lawFunctorId xs `cast` ()
  lawApplicativeComposition fall@(Succs f fs) gall@(Succs g gs) xall@(Succs x xs) =
    fmapResAppend (flip apply x) (fmap (flip apply g) (fmap compose fs)) (fmap (compose f) gs) `cast`
    lawFunctorComposition f g xs`cast`
    -- Succs (compose f g x) ((fmap (flip apply x) (fmap (flip apply g) (fmap compose fs)) `appendL`
    --                        fmap (flip apply x) (fmap (compose f) gs)) `appendL`
    --                        fmap (compose f g) xs) `cast`
    
    appendLAssoc (fmap (flip apply x) (fmap (flip apply g) (fmap compose fs)))
      (fmap (flip apply x) (fmap (compose f) gs))
      (fmap (compose f g) xs) `cast`
    -- (fmap (compose (flip apply x) (compose (flip apply g) compose)))

    lawFunctorComposition (flip apply x) (compose (flip apply g) compose) fs `cast`
    lawFunctorComposition (flip apply g) compose fs `cast`
    fmapFGEq (compose (flip apply x) (compose (flip apply g) compose)) (flip apply (g x))  fs (trivialEq0 x g) `cast`
    -- (fmap (compose (flip apply x) (compose (flip apply g) compose)) fs ==! fmap (flip apply (g x)) fs) `cast`
    -- (fmap (flip apply x) (fmap (flip apply g) (fmap compose fs)) ==!  fmap (flip apply (g x)) fs) `cast`

    lawFunctorComposition (flip apply x) (compose f) gs `cast`
    lawFunctorComposition f (flip apply x) gs `cast`
    -- works:
    -- (fmap (compose (flip apply x) (compose f)) gs ==! fmap f (fmap (flip apply x) gs)) `cast`

    -- try this
    fmapFGEq (compose (flip apply x) (compose f)) (compose f (flip apply x))   gs (trivialEq1 x f) `cast`
    (fmap (compose (flip apply x) (compose f)) gs === fmap (compose f (flip apply x)) gs) `cast`


    -- (fmap (flip apply x) (fmap (compose f) gs) ==! fmap f (fmap (flip apply x) gs)) `cast`
    -- (fmap (flip apply x) (fmap (compose f) gs) ==! fmap (compose f (flip apply x)) gs) `cast`
    
    fmapResAppend f (fmap (flip apply x) gs) (fmap g xs) `cast`
    ()
  lawApplicativeHomomorphism _ _ _ = ()
  lawApplicativeInterchange _ _ = ()
  
-- Kleisli Arrow
{-@ reflect kcompose @-}
kcompose :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
kcompose f g x = bind (f x) g


{-@ data Pair a b = Pair {projl :: a, projr :: b }  @-}
data Pair l r = Pair {projl :: l, projr :: r }
-- Writer Monad
instance Functor (Pair u) where
  fmap f (Pair u a) = (Pair u (f a))
  a <$ (Pair u _) = (Pair u a)

instance VFunctor (Pair u) where
  lawFunctorId (Pair _ _) = ()
  lawFunctorComposition _ _ _ = ()

-- instance Monoid u => Applicative (Pair u) where
--   pure x = Pair mempty x
--   ap (Pair u f) (Pair v x) = (Pair (u `mappend` v) (f x))
--   liftA2 f x y = pure f `ap` x `ap` y
--   a1 *> a2 = ap (id' <$ a1) a2
--   a1 <* a2 = liftA2 const' a1 a2

-- instance Monoid u => Monad (Pair u) where
--   bind (Pair u a) k = case k a of
--     (Pair v b) -> (Pair (mappend u v) b)
--   return = pure
--   mseq (Pair u _) (Pair v a) = (Pair (mappend u v) a)


-- {-@ data Either l r = Left l | Right r @-}
-- data Either l r = Left l | Right r
-- instance Functor (Either l) where
--   fmap f (Right x) = Right (f x)
--   fmap f (Left x) = Left x
--   x <$ (Right _) = Right x
--   _ <$ (Left x)  = Left x

-- instance VFunctor (Either l) where
--   lawFunctorId (Left _) = ()
--   lawFunctorId _ = ()
--   lawFunctorComposition _ _ _ = ()

-- instance Applicative (Either l) where
--   pure = Right 
--   ap (Right f) (Right x) = Right (f x)
--   ap (Right f) (Left x)  = Left x
--   ap (Left x) _ = Left x

--   liftA2 f x y = pure f `ap` x `ap` y
--   a1 *> a2 = ap (id' <$ a1) a2
--   a1 <* a2 = liftA2 const' a1 a2

-- instance VApplicative (Either l) where
--   lawApplicativeId (Left _) = ()
--   lawApplicativeId _ = ()
--   lawApplicativeComposition (Right _) (Right _) (Right _)  = ()
--   lawApplicativeComposition _ _ _  = ()
--   lawApplicativeHomomorphism f x (Left _) = ()
--   lawApplicativeHomomorphism f x _ = ()
--   lawApplicativeInterchange (Left _) _ = ()
--   lawApplicativeInterchange (Right _) _ = ()

-- instance Monad (Either l) where
--   return = Right
--   bind (Right x) f = f x
--   bind (Left x) f = Left x
--   mseq (Right _) (Right x) = Right x
--   mseq (Left x) _ = Left x
--   mseq (Right _) (Left x) = Left x

-- instance VMonad (Either l) where
--   lawMonad1 x f = ()
--   lawMonad2 (Left _) = ()
--   lawMonad2 _ = ()
--   lawMonad3 (Right x) f g h = h x `cast` ()
--   lawMonad3 _ _ _ _ = ()
--   lawMonadReturn _ _ = ()

-- data Const a b = Const {getConst :: a}

-- instance Functor (Const m) where
--   fmap _ (Const v) = Const v
--   _ <$ (Const v) = Const v

-- instance VFunctor (Const m) where
--   lawFunctorId (Const v) = ()
--   lawFunctorComposition _ _ _ = ()

-- data Reader r a = Reader {runReader :: r -> a}
-- {-@ reflect fmapReader @-}
-- fmapReader :: (a -> b) -> (r -> a) -> r -> b
-- fmapReader f x r = f (x r)

-- instance Functor (Reader r) where
--   fmap f (Reader x) = Reader (fmapReader f x)
--   (<$) a _ = Reader $ \r -> a

-- {-@ fmapReaderId' :: f:(r -> a) -> {fmapReader id' f == id' f}  @-}
-- fmapReaderId' :: (r -> a) -> ()
-- fmapReaderId' f =
--   axiomExt (fmapReader id' f) (id' f) $ \r -> fmapReader id' f r `cast` ()

-- {-@ lawFunctorCompositionReader :: f:(b -> c) -> g:(a -> b) -> x:(r -> a) -> {fmapReader (compose f g) x == compose (fmapReader f) (fmapReader g) x} @-}
-- lawFunctorCompositionReader :: (b -> c) -> (a -> b) -> (r -> a) -> ()
-- lawFunctorCompositionReader f g x =
--   axiomExt (fmapReader (compose f g) x)
--            (compose (fmapReader f) (fmapReader g) x)
--     $ \s ->
--         let c   = fmapReader (compose f g) x s
--             c'  = compose (fmapReader f) (fmapReader g) x s
--             c'' = x s
--         in  ()

-- instance VFunctor (Reader r) where
--   lawFunctorId (Reader f) = fmapReaderId' f
--   lawFunctorComposition f g (Reader x) = lawFunctorCompositionReader f g x


-- -- Reader
-- {-@ reflect apReader @-}
-- apReader :: (r -> a -> b) -> (r -> a) -> r -> b
-- apReader f x r = f r (x r)

-- instance Applicative (Reader r) where
--   pure x = Reader (const' x)
--   ap (Reader f) (Reader a) = Reader (apReader f a)
--   liftA2 f x y = pure f `ap` x `ap` y
--   a1 *> a2 = ap (id' <$ a1) a2
--   a1 <* a2 = liftA2 const' a1 a2

-- {-@ lawApplicativeIdReader :: v:(r -> a) -> r:r -> {apReader (const' id') v r == v r } @-}
-- lawApplicativeIdReader :: (r -> a) -> r -> ()
-- lawApplicativeIdReader v x = apReader (const' id') v x `cast` ()

-- {-@ lawApplicativeCompositionReader :: u: (r -> b -> c) -> v: (r -> a -> b) -> w: (r -> a) -> r:r ->  {apReader (apReader (apReader (const' compose) u) v) w r = apReader u (apReader v w) r} @-}
-- lawApplicativeCompositionReader
--   :: (r -> b -> c) -> (r -> a -> b) -> (r -> a) -> r -> ()
-- lawApplicativeCompositionReader u v w r = ()

-- {-@ lawApplicativeHomomorphismReader :: g:(a -> b) -> x:a -> {px: (r -> a) | px = const' x} -> r:r -> {apReader (const' g) px r = const' (g x) r} @-}
-- lawApplicativeHomomorphismReader :: (a -> b) -> a -> (r -> a) -> r -> ()
-- lawApplicativeHomomorphismReader g x px r =
--   const' x r `cast` apReader (const' g) px r `cast` px r `cast` ()

-- {-@ lawApplicativeInterchangeReader :: u: (r -> a -> b) -> y:a -> r:r -> {apReader u (const' y) r = apReader (const' (flip apply y)) u r} @-}
-- lawApplicativeInterchangeReader :: (r -> a -> b) -> a -> r -> ()
-- lawApplicativeInterchangeReader u y r = ()

-- instance VApplicative (Reader r) where
--   lawApplicativeId (Reader v) =
--     axiomExt (apReader (const' id') v) v (lawApplicativeIdReader v)
--   lawApplicativeComposition (Reader u) (Reader v) (Reader w) = axiomExt
--     (apReader (apReader (apReader (const' compose) u) v) w)
--     (apReader u (apReader v w))
--     (lawApplicativeCompositionReader u v w)
--   lawApplicativeHomomorphism g x (Reader px) = axiomExt
--     (apReader (const' g) px)
--     (const' (g x))
--     (lawApplicativeHomomorphismReader g x px)
--   lawApplicativeInterchange (Reader u) y = axiomExt
--     (apReader u (const' y))
--     (apReader (const' (flip apply y)) u)
--     (lawApplicativeInterchangeReader u y)




  --   bind :: forall a b. m a -> (a -> m b) -> m b
  -- return :: forall a. a -> m a
  -- mseq :: forall a b. m a -> m b -> m b

-- instance (VMonoid u) => VApplicative (Pair u) where
--   lawApplicativeId _ = ()
--   lawApplicativeComposition (Pair _ _) (Pair _ _) (Pair _ _)  = ()
--   lawApplicativeHomomorphism f x (Pair _ _) = ()
--   lawApplicativeInterchange (Pair _ _) _ = ()



-- data Compose f g a = Compose {getCompose :: f (g a)}

-- instance (Functor f, Functor g) => Functor (Compose f g) where
--   fmap f (Compose x) = Compose $ fmap (fmap f) x
--   x <$ m = fmap (const' x) m

-- instance (VFunctor f, VFunctor g) => VFunctor (Compose f g) where
-- --    {-@ lawFunctorId :: forall a . x:m a -> {fmap id' x == id' x} @-}
--   lawFunctorId (Compose x) =
--     (axiomExt (fmap id' :: g a -> g a) id' $ \x -> ()) `cast`
--     fmap id' (Compose x) `cast`
--     fmap (fmap id') x `cast`
--     lawFunctorId x `cast`
--     ()
--   lawFunctorComposition f g (Compose x) =
--     fmap (fmap (compose f g)) x `cast`
--     ()

--    {-@ lawFunctorComposition :: forall a b c . f:(b -> c) -> g:(a -> b) -> x:m a -> { fmap (compose f g) x == compose (fmap f) (fmap g) x } @-}
--    lawFunctorComposition :: forall a b c. (b -> c) -> (a -> b) -> m a -> ()






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







