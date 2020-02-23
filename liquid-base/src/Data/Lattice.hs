{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}

module Data.Lattice where

import Liquid.ProofCombinators 

class Lattice l where
    canFlowTo :: l -> l -> Bool
    meet :: l -> l -> l
    join :: l -> l -> l
    bot  :: l 

    {-@ lawFlowReflexivity :: l : l -> {canFlowTo l l} @-}
    lawFlowReflexivity :: l -> ()
    {-@ lawFlowAntisymmetry :: a : l -> {b : l | canFlowTo a b && canFlowTo b a} -> {a == b} @-}
    lawFlowAntisymmetry :: l -> l -> ()
    {-@ lawFlowTransitivity :: a:l -> b:l-> c:l -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c} @-}
    lawFlowTransitivity :: l -> l -> l -> ()

    {-@ lawMeet :: z : l -> x : l -> y : l -> w : l -> {z == meet x y => (canFlowTo z x && canFlowTo z y && ((canFlowTo w x && canFlowTo w y) => canFlowTo w z))} @-}
    lawMeet :: l -> l -> l -> l -> ()
    {-@ lawJoin :: x : l -> y : l -> w : l -> {(canFlowTo x (join x y) && canFlowTo y (join x y) && ((canFlowTo x w && canFlowTo y w) => canFlowTo (join x y) w))} @-}
    lawJoin :: l -> l -> l -> ()
    {-@ lawBot :: x : l -> { canFlowTo bot x } @-}
    lawBot  :: l -> ()

{-@ joinCanFlowTo 
 :: Lattice l
 => l1 : l
 -> l2 : l
 -> l3 : l
 -> {canFlowTo l1 l3 && canFlowTo l2 l3 <=> canFlowTo (join l1 l2) l3}
 @-}
joinCanFlowTo :: Lattice l => l -> l -> l -> ()
joinCanFlowTo l1 l2 l3 = lawJoin l1 l2 l3 &&& unjoinCanFlowTo l1 l2 l3 


{-@ unjoinCanFlowTo 
 :: Lattice l
 => l1:l -> l2:l -> l3:l 
 -> {canFlowTo (join l1 l2) l3 => (canFlowTo l1 l3  && canFlowTo l2 l3)}
 @-}
unjoinCanFlowTo :: Lattice l => l -> l -> l -> ()
unjoinCanFlowTo l1 l2 l3
  =     lawJoin l1 l2 l3  
    &&& lawFlowTransitivity l1 (l1 `join` l2) l3
    &&& lawFlowTransitivity l2 (l1 `join` l2) l3

{-@ notJoinCanFlowTo 
 :: Lattice l 
 => a : l 
 -> b : l 
 -> c : {l | not (canFlowTo a c)}
 -> {not (canFlowTo (join a b) c)}
 @-}
notJoinCanFlowTo :: Lattice l => l -> l -> l -> ()
notJoinCanFlowTo l1 l2 l3 = unjoinCanFlowTo l1 l2 l3

{-@ notCanFlowTo 
 :: Lattice l 
 => a : l 
 -> b : l 
 -> c : l
 -> {(not (canFlowTo b a) && canFlowTo b c) => not (canFlowTo c a)}
 @-}
notCanFlowTo :: Lattice l => l -> l -> l -> ()
notCanFlowTo a b c = lawFlowTransitivity b c a

unjoinCanFlowToItself :: Lattice l => l -> l -> ()
{-@ unjoinCanFlowToItself :: Lattice l => a:l -> b:l 
  -> { canFlowTo a (join a b) && canFlowTo b (join a b) } @-}
unjoinCanFlowToItself x y = lawJoin x y x
 
