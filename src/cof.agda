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
  [_]ᴾ : Cof → HProp₀

  cofFace : (i : Int)(e : OI) → Cof
  cofFace-[]ᴾ : (i : Int)(e : OI) → [ cofFace i e ]ᴾ ≡ (i ≈ ⟨ e ⟩)
  {-# REWRITE cofFace-[]ᴾ #-}

  cofShift : ∀{r s} → prf (r ≈> s) → Cof
  cofShift-[]ᴾ : ∀{r s} (sh : prf (r ≈> s)) → [ cofShift sh ]ᴾ ≡ (r ≈ s)
  {-# REWRITE cofShift-[]ᴾ #-}

  cof⊥ : Cof
  cof⊥-[]ᴾ : [ cof⊥ ]ᴾ ≡ ⊥
  {-# REWRITE cof⊥-[]ᴾ #-}

  cofor : (P Q : Cof) → Cof
  cofor-[]ᴾ : (P Q : Cof) → [ cofor P Q ]ᴾ ≡ ([ P ]ᴾ or [ Q ]ᴾ)
  {-# REWRITE cofor-[]ᴾ #-}

  cof⊤ : Cof
  cof⊤-[]ᴾ : [ cof⊤ ]ᴾ ≡ ⊤
  {-# REWRITE cof⊤-[]ᴾ #-}

  cof& : (P Q : Cof) → Cof
  cof&-[]ᴾ : (P Q : Cof) → [ cof& P Q ]ᴾ ≡ ([ P ]ᴾ & [ Q ]ᴾ)
  {-# REWRITE cof&-[]ᴾ #-}

  cof∀ : (P : Int → Cof) → Cof
  cof∀-[]ᴾ : (P : Int → Cof) → [ cof∀ P ]ᴾ ≡ (All i ∈ Int , [ P i ]ᴾ)
  {-# REWRITE cof∀-[]ᴾ #-}

[_] = prf ∘ [_]ᴾ

----------------------------------------------------------------------
-- Disjunction
----------------------------------------------------------------------
_∨_ = cofor

∨-rec : ∀{ℓ} (φ ψ : Cof) {C : Set ℓ}
  (p : [ φ ] → C) (q : [ ψ ] → C)
  → ((u : [ φ ])(v : [ ψ ]) → p u ≡ q v)
  → ([ φ ∨ ψ ] → C)
∨-rec φ ψ p q lap = ∥∥-elim
  (λ {(inl u) → p u;
      (inr v) → q v})
  (λ {(inl u) (inl u') → cong p (eq [ φ ]ᴾ);
      (inl u) (inr v') → lap u v' ;
      (inr v) (inl u') → symm (lap u' v);
      (inr v) (inr v') → cong q (eq [ ψ ]ᴾ)})

----------------------------------------------------------------------
-- Cofibrant-partial function classifier
----------------------------------------------------------------------
□ : Set → Set
□ A = Σ φ ∈ Cof , ([ φ ] → A)

_↗_ : {A : Set} → □ A → A → HProp₀
(φ , f) ↗ x = All u ∈ [ φ ] , f u ≈ x

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

