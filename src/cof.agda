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
module cof where 

open import prelude
open import hprop
open import logic
open import interval
open import shift

infixr 4 _∨_
infix  5 _↗_
infix  6 _∙_

postulate
  Cof : Set
  [_] : Cof → HProp₀

  cofFace : (i : Int)(e : OI) → Cof
  cofFace-[] : (i : Int)(e : OI) → [ cofFace i e ] ≡ (i ≈ ⟨ e ⟩)
  {-# REWRITE cofFace-[] #-}

  cofShift : ∀{r s} → prf (r ≈> s) → Cof
  cofShift-[] : ∀{r s} (sh : prf (r ≈> s)) → [ cofShift sh ] ≡ (r ≈ s)
  {-# REWRITE cofShift-[] #-}

  cof⊥ : Cof
  cof⊥-[] : [ cof⊥ ] ≡ ⊥
  {-# REWRITE cof⊥-[] #-}

  cofor : (P Q : Cof) → Cof
  cofor-[] : (P Q : Cof) → [ cofor P Q ] ≡ ([ P ] or [ Q ])
  {-# REWRITE cofor-[] #-}

  cof⊤ : Cof
  cof⊤-[] : [ cof⊤ ] ≡ ⊤
  {-# REWRITE cof⊤-[] #-}

  cof& : (P Q : Cof) → Cof
  cof&-[] : (P Q : Cof) → [ cof& P Q ] ≡ ([ P ] & [ Q ])
  {-# REWRITE cof&-[] #-}

  cof∀ : (P : Int → Cof) → Cof
  cof∀-[] : (P : Int → Cof) → [ cof∀ P ] ≡ (All i ∈ Int , [ P i ])
  {-# REWRITE cof∀-[] #-}

----------------------------------------------------------------------
-- Disjuntion
----------------------------------------------------------------------
_∨_ = cofor

∨-rec : ∀{ℓ} (φ ψ : Cof) {C : Set ℓ}
  (p : prf [ φ ] → C) (q : prf [ ψ ] → C)
  → ((u : prf [ φ ])(v : prf [ ψ ]) → p u ≡ q v)
  → (prf [ φ ∨ ψ ] → C)
∨-rec φ ψ p q lap = ∥∥-elim
  (λ {(inl u) → p u;
      (inr v) → q v})
  (λ {(inl u) (inl u') → cong p (equ [ φ ] u u');
      (inl u) (inr v') → lap u v' ;
      (inr v) (inl u') → symm (lap u' v);
      (inr v) (inr v') → cong q (equ [ ψ ] v v')})

----------------------------------------------------------------------
-- Cofibrant-partial function classifier
----------------------------------------------------------------------
□ : Set → Set
□ A = Σ φ ∈ Cof , (prf [ φ ] → A)

_↗_ : {A : Set} → □ A → A → HProp₀
(φ , f) ↗ x = All u ∈ prf [ φ ] , f u ≈ x

----------------------------------------------------------------------
-- Dependently typed paths
----------------------------------------------------------------------
ΠI : (Int → Set) → Set
ΠI A = (i : Int) → A i

ΠI′ :
  {A B : Int → Set}
  → ---------------------------------
  ((i : Int) → A i → B i) → ΠI A → ΠI B
ΠI′ F p i = F i (p i)

_∙_ :
  {A : Int → Set}
  → -------------------------
  □(ΠI A) → (i : Int) → □(A i)
(φ , f) ∙ i = (φ , λ u → f u i)

