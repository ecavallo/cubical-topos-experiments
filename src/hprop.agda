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

-- the following definition relies on type-in-type,
-- which is switched on only in this module

module hprop where

open import prelude

record HProp (ℓ : Level) : Set (lsuc ℓ) where
  field
    prf : Set ℓ
    equ : (u v : prf) → u ≡ v

open HProp public

HProp₀ = HProp lzero

eq : ∀ {ℓ} (P : HProp ℓ){u v : prf P} → u ≡ v
eq P {u} {v} = equ P u v
