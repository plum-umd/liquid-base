{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.List where

import           Prelude                 hiding ( foldr
                                                , foldl'
                                                )

data List a = Nil | Cons a (List a)


{-@ reflect foldl' @-}
foldl' :: (b -> a -> b) -> b -> List a -> b 
foldl' k z0 xs =
  foldr (\v fn -> {- oneShot -} (\(z) -> z `seq` fn (k z v))) (\x -> x) xs z0

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ x Nil         = x
foldr f x (Cons y ys) = foldr f (f y x) ys

-- {-@ reflect foldr @-}
-- foldr :: (a -> b -> b) -> b -> List a -> b
-- foldr k z = go
--           where
--             go Nil     = z
--             go (Cons y ys) = y `k` go ys

