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

record ShiftSet : Set₁ where
  field
    Shift : Int → Int → HProp₀

  field
    flipshift : {r s : Int} → prf (Shift r s) → prf (Shift s r)

open ShiftSet public

postulate
  compShift : ShiftSet
  fillShift : ShiftSet

open ShiftSet compShift public renaming (Shift to _~>_; flipshift to cflip)
open ShiftSet fillShift public renaming (Shift to _≈>_; flipshift to fflip)

postulate
  O~>I : prf (O ~> I)
  shiftCompToFill : {r s : Int} → prf (r ~> s) → ((i : Int) → prf (r ≈> i))
