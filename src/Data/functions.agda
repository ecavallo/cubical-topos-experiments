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
Π' : {Γ : Set}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

FibΠid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠid {A} {B} α β p r s sh φ f g = g₁ , (extends , trivial)
  where
  pₐ : (a : A (p s)) → ΠI (A ∘ p)
  pₐ a i = fst (compToFill (A ∘ p) (α p) s i (shiftCompToFill (cflip sh) i) cof⊥ ∅-elim (a , λ u → ∅-elim u))

  pₐs≡a : (a : A (p s)) → pₐ a s ≡ a
  pₐs≡a a = symm (snd (snd (compToFill (A ∘ p) (α p) s s (shiftCompToFill (cflip sh) s) cof⊥ ∅-elim (a , λ u → ∅-elim u))) refl)

  q : (a : A (p s)) → Int → Σ Int A
  q a i = (p i , pₐ a i)

  f' : (a : A (p s)) → [ φ ] → ΠI (B ∘ (q a))
  f' a u i = f u i (pₐ a i)

  b₀ : (a : A (p s)) → ⟦ b ∈ (B (q a r)) ∣ (φ , f' a) ∙ r ↗ b ⟧
  b₀ a = (fst g (pₐ a r) , (λ u → cong (λ f → f (pₐ a r)) (snd g u)))

  abstract
    g₁ : (Π' A B) (p s)
    g₁ a = subst (λ a → B (p s , a)) (pₐs≡a a) (fst (β (q a) r s sh φ (f' a) (b₀ a)))

  abstract
    extends : prf ((φ , f) ∙ s ↗ g₁)
    extends u = funext (λ a → substLemma (pₐs≡a a) (trans (f's≡g₁ a) (fs≡f's a))) where
      substLemma : {a a' : A (p s)}(eq : a' ≡ a){b : B (p s , a)}{b' : B (p s , a')}
        → subst (λ a → B (p s , a)) (symm eq) b ≡ b' → b ≡ subst (λ a → B (p s , a)) eq b'
      substLemma refl refl = refl

      f's≡g₁ : (a : A (p s)) → f' a u s ≡ fst (β (q a) r s sh φ (f' a) (b₀ a))
      f's≡g₁ a = fst (snd (β (q a) r s sh φ (f' a) (b₀ a))) u

      fs≡f's : (a : A (p s)) → subst (λ a₁ → B (p s , a₁)) (symm (pₐs≡a a)) (snd ((φ , f) ∙ s) u a) ≡ f' a u s
      fs≡f's a = congdep (λ a' → f u s a') (symm (pₐs≡a a))

  abstract
    trivial : (eq : r ≡ s) → subst (Π' A B ∘ p) eq (fst g) ≡ g₁
    trivial refl = funext λ a →
      trans
        (cong (subst (λ a → B (p s , a)) (pₐs≡a a)) (snd (snd (β (q a) r r sh φ (f' a) (b₀ a))) refl))
        (symm (congdep (fst g) (pₐs≡a a)))


FibΠ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
FibΠ {Γ} {A} {B} α β p = FibΠid (reindex A α p) (reindex B β (p ×id)) id

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
reindexΠ A B α β ρ = refl
