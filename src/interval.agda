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
module interval where 

open import prelude
open import hprop
open import logic

----------------------------------------------------------------------
-- Interval
----------------------------------------------------------------------
open import Agda.Builtin.TrustMe
postulate
  Int   : Set
  O     : Int
  I     : Int
  O≠I   : O ≡ I → ∅
  cntd   : (P : Int → HProp₀) → ((i : Int) → prf(P i or ¬(P i))) → (i : Int) → P i ≡ P I

-- Type for representing just the endpoints O and I
data OI : Set where
  O' : OI
  I' : OI

! : OI → OI
! O' = I'
! I' = O'

!!e=e : (e : OI) → ! (! e) ≡ e
!!e=e O' = refl
!!e=e I' = refl

{-# REWRITE !!e=e #-}

⟨_⟩ : (e : OI) → Int
⟨ O' ⟩ = O
⟨ I' ⟩ = I

e≠!e : {A : Set}{e : OI} → ⟨ e ⟩ ≡ ⟨ ! e ⟩ → A
e≠!e {A} {O'} p = ∅-elim (O≠I p)
e≠!e {A} {I'} p = ∅-elim (O≠I (symm p))

OIinj : (i : Int)(e : OI) → i ≡ ⟨ e ⟩ → (i ≡ O) ⊎ (i ≡ I)
OIinj _ O' p = inl p
OIinj _ I' q = inr q

-- Functions for performing case analysis on endpoints
-- In one variable:
OI-elim :
  {i : Int}
  {B : Set}
  (f : (i ≡ O) ⊎ (i ≡ I) → B)
  → ---------------------------
  prf (i ≈ O or i ≈ I) → B
OI-elim {i} f u = ∥∥-elim f casesAgree u where
  casesAgree : (x x' : (i ≡ O) ⊎ (i ≡ I)) → f x ≡ f x'
  casesAgree (inl i≡O) (inl i≡O') = cong (f ∘ inl) uipImp 
  casesAgree (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree (inr i≡I) (inr i≡I') = cong (f ∘ inr) uipImp

e!e-elim :
  {i : Int}
  {B : Set}
  {e : OI}
  (f : (i ≡ ⟨ e ⟩) ⊎ (i ≡ ⟨ ! e ⟩) → B)
  → ---------------------------
  prf (i ≈ ⟨ e ⟩ or i ≈ ⟨ ! e ⟩) → B
e!e-elim {e = O'} = OI-elim
e!e-elim {i }{e = I'} f u = OI-elim (λ{ (inl x) → f (inr x) ; (inr x) → f (inl x) })
  (∥∥-elim (λ{ (inl x) → ∣ inr x ∣ ; (inr x) → ∣ inl x ∣ }) (λ x x' → eq (i ≈ ⟨ O' ⟩ or i ≈ ⟨ I' ⟩)) u)

-- The dependent version:
OI-elim-dep :
  {i : Int}
  {B : prf (i ≈ O or i ≈ I) → Set _}
  (f : (v : (i ≡ O) ⊎ (i ≡ I)) → B ∣ v ∣ )
  → ---------------------------
  (u : prf (i ≈ O or i ≈ I)) → B u
OI-elim-dep {i} {B} f u = OI-elim cases u where
  cases : (i ≡ O) ⊎ (i ≡ I) → B u
  cases (inl i≡O) = subst B (equ (i ≈ O or i ≈ I) ∣ inl i≡O ∣ u) (f (inl i≡O))
  cases (inr i≡I) = subst B (equ (i ≈ O or i ≈ I) ∣ inr i≡I ∣ u) (f (inr i≡I))

-- And in two variables:
OI-elim' :
  {i j : Int}
  {B : Set}
  (f : (i ≡ O) ⊎ (i ≡ I) → B)
  (g : (j ≡ O) ⊎ (j ≡ I) → B)
  (corners : (e e' : OI)(p : i ≡ ⟨ e ⟩)(q : j ≡ ⟨ e' ⟩) → f (OIinj i e p) ≡ g (OIinj j e' q))
  → ---------------------------
  prf ((i ≈ O or i ≈ I) or (j ≈ O or j ≈ I)) → B
OI-elim' {i} {j} {B} f g corners u = ∥∥-elim split corners' u where
  casesAgree : {i : Int}(f : (i ≡ O) ⊎ (i ≡ I) → B)(x x' : (i ≡ O) ⊎ (i ≡ I)) → f x ≡ f x'
  casesAgree f (inl i≡O) (inl i≡O') = cong (f ∘ inl) uipImp 
  casesAgree _ (inl i≡O) (inr i≡I) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree _ (inr i≡I) (inl i≡O) = ∅-elim (O≠I (trans i≡I (symm i≡O)))
  casesAgree f (inr i≡I) (inr i≡I') = cong (f ∘ inr) uipImp 
  split :  prf (i ≈ O or i ≈ I) ⊎ prf (j ≈ O or j ≈ I) → B
  split (inl iOI) = ∥∥-elim f (casesAgree f) iOI
  split (inr jOI) = ∥∥-elim g (casesAgree g) jOI
  corners' : (x x' : prf (i ≈ O or i ≈ I) ⊎ prf (j ≈ O or j ≈ I)) → split x ≡ split x'
  corners' (inl u) (inl v) = cong (λ x → split (inl x)) (equ (i ≈ O or i ≈ I) u v)
  corners' (inl u) (inr v) = or-elim-eq (split ∘ inl) (split (inr v))
    (λ i≡O → symm (or-elim-eq (split ∘ inr) (split (inl ∣ inl i≡O ∣))
      (λ j≡O → symm (corners O' O' i≡O j≡O))
      (λ j≡I → symm (corners O' I' i≡O j≡I)) v))
    ((λ i≡I → symm (or-elim-eq (split ∘ inr) (split (inl ∣ inr i≡I ∣))
      (λ j≡O → symm (corners I' O' i≡I j≡O))
      (λ j≡I → symm (corners I' I' i≡I j≡I)) v)))
    u
  corners' (inr u) (inl v) = or-elim-eq (split ∘ inr) (split (inl v))
    (λ j≡O → symm (or-elim-eq (split ∘ inl) (split (inr ∣ inl j≡O ∣))
      (λ i≡O → corners O' O' i≡O j≡O)
      (λ i≡I → corners I' O' i≡I j≡O) v))
    (λ j≡I → symm (or-elim-eq (split ∘ inl) (split (inr ∣ inr j≡I ∣))
      (λ i≡O → corners O' I' i≡O j≡I)
      (λ i≡I → corners I' I' i≡I j≡I) v))
    u
  corners' (inr u) (inr v) = cong (λ x → split (inr x)) (equ (j ≈ O or j ≈ I) u v)
