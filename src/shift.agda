----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper "Axioms for
-- Modelling Cubical Type Theory in a Topos" (CSL Special Issue
-- version). 
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module shift where 

open import prelude
open import hprop
open import logic
open import interval

record ShapeSet : Set₁ where
  field
    Shape : Set₀
    Loc : Shape → Set₀
    int : Shape
    Loc-int : Loc int ≡ Int
    
postulate
  shapeSet : ShapeSet

open ShapeSet shapeSet public
{-# REWRITE Loc-int #-}

record ShiftSet : Set₁ where
  field
    Shift : (S : Shape) → Loc S → Loc S → HProp₀
    flipshift : (S : Shape) {r s : Loc S} → prf (Shift S r s) → prf (Shift S s r)

open ShiftSet public

postulate
  compShift : ShiftSet
  fillShift : ShiftSet

open ShiftSet compShift public renaming (Shift to _∋_~>_; flipshift to cflip)
open ShiftSet fillShift public renaming (Shift to _∋_≈>_; flipshift to fflip)

postulate
  O~>I : prf (int ∋ O ~> I)
  shiftCompToFill : (S : Shape) {r s : Loc S} → prf (S ∋ r ~> s) → ((i : Loc S) → prf (S ∋ r ≈> i))
