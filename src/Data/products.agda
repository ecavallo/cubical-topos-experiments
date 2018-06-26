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
module Data.products where 

open import prelude
open import interval
open import hprop
open import logic
open import shift
open import cof
open import fibrations
  
----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------
Σ' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Σ' A B x = Σ a ∈ A x , B (x , a)

abstract
  FibΣid :
   {A : Int → Set}
   {B : (Σ x ∈ Int , A x) → Set}
   (α : isFib A)
   (β : isFib B)
   → -----------
   isFib (Σ' A B)
  FibΣid {A} {B} α β p r s sh φ f ((a₀ , b₀) , extendsF) =
    (fst (aᵢ s) , fst b₁) , (extends , trivial)
    where
    g : [ φ ] → ΠI (A ∘ p)
    g u i = fst (f u i)

    a₀ExtendsG : prf ((φ , g) ∙ r ↗ a₀)
    a₀ExtendsG u = cong fst (extendsF u)

    aᵢ : (i : Int) → ⟦ p' ∈ (A ∘ p) i ∣ ((φ , g) ∙ i ↗ p') & (All eq ∈ (r ≡ i) , subst (A ∘ p) eq a₀ ≈ p') ⟧
    aᵢ i = compToFill (A ∘ p) (α p) r i (shiftCompToFill sh i) φ g (a₀ , a₀ExtendsG)

    q : Int → (Σ x ∈ Int , A x)
    q i = (p i , fst (aᵢ i))

    h : [ φ ] → ΠI (B ∘ q)
    h u i = subst (λ a → B (p i , a)) (fst (snd (aᵢ i)) u) (snd (f u i))

    b₀' : (B ∘ q) r
    b₀' = subst (λ a → B (p r , a)) (snd (snd (aᵢ r)) refl) b₀

    b₀'ExtendsH : prf ((φ , h) ∙ r ↗ b₀')
    b₀'ExtendsH u =
      transLift
        (snd (snd (aᵢ r)) refl)
        (Σeq₁ (extendsF u))
        (fst (snd (aᵢ r)) u)
        (Σeq₂ (extendsF u))

      where
      transLift :
        {i : Int}
        {Bᵢ : A (p i) → Set}
        {x y z : A (p i)}
        (q : y ≡ z)
        (p : x ≡ y)
        (r : x ≡ z)
        {bx : Bᵢ x}
        {by : Bᵢ y}
        (s : subst Bᵢ p bx ≡ by)
        → ---------
        subst Bᵢ r bx ≡ subst Bᵢ q by
      transLift refl refl refl refl = refl

    b₁ : ⟦ b ∈ (B ∘ q) s ∣ (φ , h) ∙ s ↗ b & (All eq ∈ (r ≡ s) , subst (B ∘ q) eq b₀' ≈ b) ⟧
    b₁ = β q r s sh φ h (b₀' , b₀'ExtendsH)

    extends : prf ((φ , f) ∙ s ↗ (fst (aᵢ s) , fst b₁))
    extends u = Σext (fst (snd (aᵢ s)) u) (fst (snd b₁) u)

    trivial : (eq : r ≡ s) → subst (λ i → Σ' A B (p i)) eq (a₀ , b₀) ≡ (fst (aᵢ s) , fst b₁)
    trivial refl = Σext (snd (snd (aᵢ s)) refl) (snd (snd b₁) refl)

_×id : {A A' : Set}{B : A' → Set}(f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) (a , b) = (f a , b)

FibΣ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
FibΣ {Γ} {A} {B} α β p = FibΣid (reindex A α p) (reindex B β (p ×id)) id

FibΣ' :
  {Γ : Set}
  (A : Fib Γ)
  (B : Fib (Σ x ∈ Γ , fst A x))
  → -----------
  Fib Γ
FibΣ' (A , α) (B , β) = Σ' A B , FibΣ {A = A} {B = B} α β

-- ----------------------------------------------------------------------
-- Forming Σ-types is stable under reindexing
----------------------------------------------------------------------
reindexΣ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Σ' A B) (FibΣ {B = B} α β) ρ ≡ FibΣ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΣ A B α β ρ = refl
