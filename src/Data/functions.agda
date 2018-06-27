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
module Data.functions where

open import prelude
open import interval
open import hprop
open import logic
open import shift
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
Π' : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

FibΠ : ∀{ℓ}{Γ : Set ℓ}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠ {Γ = Γ} {A} {B} α β S p r s sh φ f g = g₁ , (extends , trivial)
  where
  pₐ : (a : A (p s)) → Π (Loc S) (A ∘ p)
  pₐ a i = fst (compToFill S (A ∘ p) (α S p) s i (shiftCompToFill S (cflip S sh) i) cof⊥ ∅-elim (a , λ u → ∅-elim u))

  pₐs≡a : (a : A (p s)) → pₐ a s ≡ a
  pₐs≡a a = symm (snd (snd (compToFill S (A ∘ p) (α S p) s s (shiftCompToFill S (cflip S sh) s) cof⊥ ∅-elim (a , λ u → ∅-elim u))) refl)

  q : (a : A (p s)) → (Loc S) → Σ Γ A
  q a i = (p i , pₐ a i)

  f' : (a : A (p s)) → [ φ ] → Π (Loc S) (B ∘ (q a))
  f' a u i = f u i (pₐ a i)

  b₀ : (a : A (p s)) → ⟦ b ∈ (B (q a r)) ∣ (φ , f' a) ∙ r ↗ b ⟧
  b₀ a = (fst g (pₐ a r) , (λ u → cong (λ f → f (pₐ a r)) (snd g u)))

  g₁ : (Π' A B) (p s)
  g₁ a = subst (λ a → B (p s , a)) (pₐs≡a a) (fst (β S (q a) r s sh φ (f' a) (b₀ a)))

  abstract
    extends : prf ((φ , f) ∙ s ↗ g₁)
    extends u = funext (λ a → substLemma (pₐs≡a a) (trans (f's≡g₁ a) (fs≡f's a))) where
      substLemma : {a a' : A (p s)}(eq : a' ≡ a){b : B (p s , a)}{b' : B (p s , a')}
        → subst (λ a → B (p s , a)) (symm eq) b ≡ b' → b ≡ subst (λ a → B (p s , a)) eq b'
      substLemma refl refl = refl

      f's≡g₁ : (a : A (p s)) → f' a u s ≡ fst (β S (q a) r s sh φ (f' a) (b₀ a))
      f's≡g₁ a = fst (snd (β S (q a) r s sh φ (f' a) (b₀ a))) u

      fs≡f's : (a : A (p s)) → subst (λ a₁ → B (p s , a₁)) (symm (pₐs≡a a)) (snd ((φ , f) ∙ s) u a) ≡ f' a u s
      fs≡f's a = congdep (λ a' → f u s a') (symm (pₐs≡a a))

  abstract
    trivial : (eq : r ≡ s) → subst (Π' A B ∘ p) eq (fst g) ≡ g₁
    trivial refl = funext λ a →
      trans
        (cong (subst (λ a → B (p s , a)) (pₐs≡a a)) (snd (snd (β S (q a) r r sh φ (f' a) (b₀ a))) refl))
        (symm (congdep (fst g) (pₐs≡a a)))

FibΠ' :
  {Γ : Set}
  (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΠ' (A , α) (B , β) = (Π' A B , FibΠ {A = A} {B = B} α β)

Πext : {Γ : Set}{A : Γ → Set}{B : (Σ x ∈ Γ , A x) → Set}{x : Γ}{f g : Π' A B x} → ((a : A x) → f a ~ g a) → f ~ g
fst (Πext pointwise) i a = fst (pointwise a) i
fst (snd (Πext pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (Πext pointwise)) = funext (λ a → snd (snd (pointwise a)))
  
-- ----------------------------------------------------------------------
-- Forming Π-types is stable under reindexing
----------------------------------------------------------------------
reindexΠ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Π' A B) (FibΠ {B = B} α β) ρ ≡ FibΠ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΠ A B α β ρ = fibExt (Π' A B ∘ ρ) (λ S p r s sh φ f x₁ → refl)
