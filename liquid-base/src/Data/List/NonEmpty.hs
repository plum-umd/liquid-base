{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Data.List.NonEmpty where

import           Prelude ()

import           Data.List

data NonEmpty a = NonEmpty a (List a)
