{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Lattice where

{-@
data Lattice l = CLattice {
    canFlowTo :: l -> l -> Bool
  , join :: l -> l -> l
  , lawJoin :: x : l -> y : l -> w : l -> {(canFlowTo x (join x y) && canFlowTo y (join x y) && ((canFlowTo x w && canFlowTo y w) => canFlowTo (join x y) w))}
  , lawFlowTransitivity :: a:l -> b:l-> c:l -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c}
  }
@-}
data Lattice l = CLattice {
    canFlowTo :: l -> l -> Bool
  , join :: l -> l -> l
  , lawJoin :: l -> l -> l -> ()
  , lawFlowTransitivity :: l -> l -> l -> ()
  }

{-@ unjoinCanFlowTo 
 :: d:Lattice l
 -> l1:l -> l2:l -> l3:l 
 -> {canFlowTo d (join d l1 l2) l3 => (canFlowTo d l1 l3  && canFlowTo d l2 l3)}
 @-}
unjoinCanFlowTo :: Lattice l -> l -> l -> l -> ()
unjoinCanFlowTo d l1 l2 l3
  | canFlowTo d (join d l1 l2) l3 = 
        lawJoin d l1 l2 l3  
    `k` lawFlowTransitivity d l1 (join d l1 l2) l3
    `k` lawFlowTransitivity d l2 (join d l1 l2) l3
  | otherwise = 
        ()

{-@ reflect k @-}
k :: () -> () -> ()
k () () = ()

