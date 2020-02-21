{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.List where

import           Prelude ()

data List a = Nil | Cons a (List a)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ x Nil         = x
foldr f x (Cons y ys) = foldr f (f y x) ys

