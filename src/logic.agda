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
module logic where

open import prelude
open import hprop public

infix  1 exists all exists!
infixr 3 _⊃_ _or_ _&_
infix  4 _≈_ 

----------------------------------------------------------------------
-- Function extensionality using primTrustMe
----------------------------------------------------------------------
open import Agda.Builtin.TrustMe

funext :
   {ℓ ℓ' : Level}
   {A : Set ℓ}
   {B : A → Set ℓ'}
   {f g : (x : A) → B x}
   → ----------------------------
   ((x : A) → f x ≡ g x) → f ≡ g
funext _ = primTrustMe

----------------------------------------------------------------------
-- Proposition extensionality using primTrustMe
----------------------------------------------------------------------
-- propext : ∀{ℓ}
--   {P Q : HProp ℓ}
--   → ---------------------------------------
--   (prf P → prf Q) → (prf Q → prf P) → P ≡ Q
-- propext _ _ = primTrustMe

----------------------------------------------------------------------
-- Comprehension
----------------------------------------------------------------------
set : ∀{ℓ m} (A : Set ℓ)(P : A → HProp m) → Set (ℓ ⊔ m)
set A P = Σ x ∈ A , prf (P x)

inc : ∀{ℓ m} {A : Set ℓ}(P : A → HProp m) → set A P → A
inc _ = fst 

syntax set A (λ x → P) = ⟦ x ∈ A ∣ P ⟧

incMono : ∀{ℓ m}
   {A : Set ℓ}
   (P : A → HProp m)
   → -----------------------------------------
   (a b : set A P) → inc P a ≡ inc P b → a ≡ b
incMono P (x , u) (.x , v) refl = cong (_,_ x) (equ (P x) u v)

----------------------------------------------------------------------
-- Equality 
----------------------------------------------------------------------
_≈_ : ∀{ℓ} {A : Set ℓ} → A → A → HProp ℓ
prf (x ≈ y) = x ≡ y
equ (_ ≈ _) = uip 

----------------------------------------------------------------------
-- Universal quantifier
----------------------------------------------------------------------
all : ∀{ℓ m} (A : Set ℓ) → (A → HProp m) → HProp (ℓ ⊔ m)
prf (all A P)     = (x : A) → prf (P x)
equ (all A P) f g = funext (λ x → equ (P x) (f x) (g x))

syntax all A (λ x → P) = All x ∈ A , P

----------------------------------------------------------------------
-- Implication
----------------------------------------------------------------------
_⊃_ : ∀{ℓ m} → HProp ℓ → HProp m → HProp (ℓ ⊔ m)
prf (P ⊃ Q)     = prf P → prf Q
equ (P ⊃ Q) f g = funext (λ x → equ Q (f x) (g x))

-- ----------------------------------------------------------------------
-- Truth
----------------------------------------------------------------------
⊤ : HProp₀
prf ⊤ = Unit
equ ⊤ tt tt = refl

-- ----------------------------------------------------------------------
-- Conjunction
----------------------------------------------------------------------
_&_ : ∀{ℓ m} → HProp ℓ → HProp m → HProp (ℓ ⊔ m)
prf (P & Q)                     = prf P × prf Q
equ (P & Q) (u₁ , u₂) (v₁ , v₂) =
  Σext (equ P u₁ v₁)
  (equ Q (subst (λ _ → prf Q) (equ P u₁ v₁) u₂) v₂)

----------------------------------------------------------------------
-- Falsity
----------------------------------------------------------------------
⊥ : HProp₀
prf ⊥  = ∅
equ ⊥ () _

-- ----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------
¬ : ∀{ℓ} → HProp ℓ → HProp ℓ
¬ P = P ⊃ ⊥

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------
postulate
  ∥_∥ : ∀{ℓ} → Set ℓ → HProp ℓ
  ∣_∣ : ∀{ℓ}{A : Set ℓ} → A → prf ∥ A ∥

  ∥∥-elim : ∀{ℓ m}
    {A : Set ℓ} {B : Set m}
    (f : A → B)
    (e : (x x' : A) → f x ≡ f x')
    → ---------------------------
    prf ∥ A ∥ → B

  ∥∥-elim-∣∣ : ∀{ℓ m}
    {A : Set ℓ} {B : Set m}
    (f : A → B)
    (e : (x x' : A) → f x ≡ f x')
    (a : A)
    → ---------------------------
    ∥∥-elim f e ∣ a ∣ ≡ f a
  {-# REWRITE ∥∥-elim-∣∣ #-}

∥∥-rec : ∀{ℓ m}
  {A : Set ℓ}
  (P : HProp m)
  (f : A → prf P)
  → ---------------
  prf ∥ A ∥ → prf P
∥∥-rec P f = ∥∥-elim f (λ x x' → equ P (f x) (f x'))

----------------------------------------------------------------------
-- Disjunction
----------------------------------------------------------------------
_or_ : ∀{ℓ m} → HProp ℓ → HProp m → HProp (ℓ ⊔ m)
P or Q =  ∥ prf P ⊎ prf Q ∥

orl : ∀{ℓ}{P Q : HProp ℓ} → prf P → prf (P or Q)
orl p = ∣ inl p ∣

orr : ∀{ℓ}{P Q : HProp ℓ} → prf Q → prf (P or Q)
orr q = ∣ inr q ∣

----------------------------------------------------------------------
-- Existential quantifier
----------------------------------------------------------------------
exists : ∀{ℓ m}(A : Set ℓ) → (A → HProp m) → HProp (ℓ ⊔ m)
exists A P = ∥ Σ x ∈ A , prf (P x) ∥

syntax exists A (λ x → P) = ∃ x ∈ A , P

----------------------------------------------------------------------
-- or-elim
----------------------------------------------------------------------
or-elim : ∀{ℓ m n}
  {A : Set ℓ} {B : Set m}
  (C : prf ∥ A ⊎ B ∥ → Set n)
  (is-prop : (u : prf ∥ A ⊎ B ∥) → (c c' : C u) → c ≡ c')
  (p : (a : A) → C ∣ inl a ∣)
  (q : (b : B) → C ∣ inr b ∣)
  → ---------------------------
  (u : prf ∥ A ⊎ B ∥) → C u
or-elim {A = A} {B} C is-prop p q u = ∥∥-elim cases (λ x y → is-prop u (cases x) (cases y)) u where
  cases : A ⊎ B → C u
  cases (inl a) = subst C (eq ∥ A ⊎ B ∥) (p a)
  cases (inr b) = subst C (eq ∥ A ⊎ B ∥) (q b)

or-elim-eq : ∀{ℓ m n}
  {A : Set ℓ} {B : Set m} {C : Set n}
  (f : prf ∥ A ⊎ B ∥ → C)
  (c : C)
  (p : (l : A) → f ∣ inl l ∣ ≡ c)
  (q : (r : B) → f ∣ inr r ∣ ≡ c)
  → ---------------------------
  (u : prf ∥ A ⊎ B ∥) → f u ≡ c
or-elim-eq {A = A} {B} {C} f c p q u = ∥∥-elim cases uip' u where
  cases : A ⊎ B → f u ≡ c
  cases (inl l) = subst (λ u → f u ≡ c) (equ ∥ A ⊎ B ∥ ∣ inl l ∣ u) (p l)
  cases (inr r) = subst (λ u → f u ≡ c) (equ ∥ A ⊎ B ∥ ∣ inr r ∣ u) (q r)
  uip' : (x x' : A ⊎ B) → cases x ≡ cases x'
  uip' x x' = uip (cases x) (cases x')

----------------------------------------------------------------------
-- Unique existence
----------------------------------------------------------------------
exists! : ∀{ℓ m} (A : Set ℓ) → (A → HProp m) → HProp (ℓ ⊔ m)
exists! A P = ∃ x ∈ A , P x & (All x' ∈ A , P x' ⊃ x ≈ x')

syntax exists! A (λ x → P) = ∃! x ∈ A , P

----------------------------------------------------------------------
-- Axiom of description
----------------------------------------------------------------------
axd : ∀ {ℓ m}
  {A : Set ℓ}
  (P : A → HProp m)
  → ----------------------------------------
  prf (∃! x ∈ A , P x) → Σ x ∈ A , prf (P x)

axd {ℓ} {m} {A} P u = ∥∥-elim f e u where

  B : Set (ℓ ⊔ m)
  B = Σ x ∈ A , prf (P x) × ((x' : A) → prf (P x') → x ≡ x')
  
  f : B → (Σ x ∈ A , prf (P x))
  f (x , u , _) = (x , u)

  e : (y y' : B) → f y ≡ f y'
  e (_ , _ , g) (x' , u' , _) = Σext (g x' u') (eq (P x'))

