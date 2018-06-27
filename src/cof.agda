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

  cofShift : (S : Shape) {r s : Loc S} → prf (S ∋ r ≈> s) → Cof
  cofShift-[]ᴾ : (S : Shape) {r s : Loc S} (sh : prf (S ∋ r ≈> s))
    → [ cofShift S sh ]ᴾ ≡ (r ≈ s)
  {-# REWRITE cofShift-[]ᴾ #-}

  cof⊥ : Cof
  cof⊥-[]ᴾ : [ cof⊥ ]ᴾ ≡ ⊥
  {-# REWRITE cof⊥-[]ᴾ #-}

  cofor : (P Q : Cof) → Cof
  cofor-[]ᴾ : (P Q : Cof)
    → [ cofor P Q ]ᴾ ≡ ([ P ]ᴾ or [ Q ]ᴾ)
  {-# REWRITE cofor-[]ᴾ #-}

  cof⊤ : Cof
  cof⊤-[]ᴾ : [ cof⊤ ]ᴾ ≡ ⊤
  {-# REWRITE cof⊤-[]ᴾ #-}

  cof& : (P Q : Cof) → Cof
  cof&-[]ᴾ : (P Q : Cof)
    → [ cof& P Q ]ᴾ ≡ ([ P ]ᴾ & [ Q ]ᴾ)
  {-# REWRITE cof&-[]ᴾ #-}

  cof∀ : (S : Shape) (P : Loc S → Cof) → Cof
  cof∀-[]ᴾ : (S : Shape) (P : Loc S → Cof)
    → [ cof∀ S P ]ᴾ ≡ (All r ∈ Loc S , [ P r ]ᴾ)
  {-# REWRITE cof∀-[]ᴾ #-}

[_] = prf ∘ [_]ᴾ

postulate
  cofExt : {φ ψ : Cof} → ([ φ ] → [ ψ ]) → ([ ψ ] → [ φ ]) → φ ≡ ψ

cofFace : (i : Int)(e : OI) → Cof
cofFace i O' = cofShift int (fflip int (shiftCompToFill int O~>I i))
cofFace i I' = cofShift int (fflip int (shiftCompToFill int (cflip int O~>I) i))

cofCShift : (S : Shape) {r s : Loc S} → prf (S ∋ r ~> s) → Cof
cofCShift S {r} {s} sh = cofShift S (shiftCompToFill S sh s)

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
  {A : Set}
  {B : A → Set}
  → -------------------------
  □(Π A B) → (r : A) → □(B r)
(φ , f) ∙ i = (φ , λ u → f u i)

