{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.List where

import           Prelude                 hiding ( foldr
                                                )

data List a = Nil | Cons a (List a)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ x Nil         = x
foldr f x (Cons y ys) = f y (foldr f x ys)

{-@ reflect foldl' @-}
foldl' :: (b -> a -> b) -> b -> List a -> b
foldl' _ x Nil         = x
foldl' f x (Cons y ys) = foldl' f (f x y) ys
