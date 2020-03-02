module Data.Endo where

{-@ data Endo a = Endo (a -> a) @-}
data Endo a = Endo (a -> a)
