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
module Data.paths where

open import prelude
open import interval
open import hprop
open import logic
open import shift
open import cof
open import fibrations
open import Data.products

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------
_~~_ : {A : Int → Set}(a : A O)(a' : A I) → Set
_~~_ {A} a a' = ⟦ p ∈ (ΠI A) ∣ (p O ≈ a) & (p I ≈ a') ⟧

_at_ : {A : Int → Set}{a : A O}{a' : A I}(p : a ~~ a')(i : Int) → A i
(p , _) at i = p i

atO : {A : Int → Set}{a : A O}{a' : A I}(p : _~~_ {A} a a') → p at O ≡ a
atO p = fst (snd p)

atI : {A : Int → Set}{a : A O}{a' : A I}(p : _~~_ {A} a a') → p at I ≡ a'
atI p = snd (snd p)

_~_ : {A : Set}(a a' : A) → Set
_~_ {A} a a' = _~~_ {A = λ _ → A} a a'

-- transDep : {A : Int → Set}{α : isFib A}{a a' : A O}{b : A I} → (a ~~ b) → (a' ~~ b) → (a ~ a')
-- transDep {A} {α} {a} {a'} {b} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
--   f : (i : Int) → prf [ cofFace i O' ∨ cofFace i I' ] → ΠI A
--   f i u j = OI-elim cases u where
--     cases : (i ≡ O) ⊎ (i ≡ I) → A j
--     cases (inl _) = p j
--     cases (inr _) = q j
    
--   r : (i : Int) → ⟦ a ∈ (A O) ∣ (cofFace i O' ∨ cofFace i I' , f i) ∙ O ↗ a ⟧
--   r i = {!α !} --α I' id (? ∨ ?) (f i) (b , or-elim-eq (λ u → f i u I) b pI qI)

--   rO≡a : fst (r O) ≡ a
--   rO≡a = trans pO (symm (snd (r O) ∣ inl refl ∣))

--   rI≡a' : fst (r I) ≡ a'
--   rI≡a' = trans qO (symm (snd (r I) ∣ inr refl ∣))

-- transDep' : {A : Int → Set}{α : isFib A}{a : A O}{b b' : A I} → (a ~~ b) → (a ~~ b') → (b ~ b')
-- transDep' {A} {α} {a} {b} {b'} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
--   f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π A
--   f i u j = OI-elim cases u where
--     cases : (i ≡ O) ⊎ (i ≡ I) → A j
--     cases (inl _) = p j
--     cases (inr _) = q j
    
--   r : (i : Int) → ⟦ b ∈ (A I) ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ b ⟧
--   r i = α O' id (i ≈O ∨ i ≈I) (f i) (a , or-elim-eq (λ u → f i u O) a pO qO)

--   rO≡a : fst (r O) ≡ b
--   rO≡a = trans pI (symm (snd (r O) ∣ inl refl ∣))

--   rI≡a' : fst (r I) ≡ b'
--   rI≡a' = trans qI (symm (snd (r I) ∣ inr refl ∣))

-- transPath : {A : Set}(α : isFib {Γ = Unit} (λ _ → A)){x y z : A} → x ~ y → y ~ z → x ~ z
-- transPath {A} α {x} {y} {z} p q = ((λ i → fst (r i)) , rO≡x , rI≡z) where
--   f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ _ → A)
--   f i u j = OI-elim cases u where
--     cases : (i ≡ O) ⊎ (i ≡ I) → A
--     cases (inl _) = x 
--     cases (inr _) = fst q j
  
--   qO=pI : (i : Int)(eq : i ≡ I) → fst q O ≡ fst p i
--   qO=pI .I refl = trans (symm (snd (snd p))) (fst (snd q))

--   pO=pi : (i : Int)(l : i ≡ O) → fst p O ≡ fst p i
--   pO=pi .O refl = refl
  
--   r : (i : Int) → ⟦ a ∈ A ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ a ⟧
--   r i = α O' (λ _ → tt) (i ≈O ∨ i ≈I) (f i)
--     ((fst p i , or-elim-eq (λ u → f i u O) (fst p i) (λ {l} → trans (pO=pi i l) (symm (fst (snd p)))) (λ {r} → qO=pI i r)))

--   rO≡x : fst (r O) ≡ x
--   rO≡x = symm (snd (r O) ∣ inl refl ∣)

--   rI≡z : fst (r I) ≡ z
--   rI≡z = trans (snd (snd q)) (symm (snd (r I) ∣ inr refl ∣))

-- congPath :
--   {A : Set}
--   {B : Set}
--   (f : A → B)
--   {x y : A}
--   (p : x ~ y)
--   → -----------
--   f x ~ f y
-- congPath f p = ((f ∘ (fst p)) , (cong f (fst (snd p))) , cong f (snd (snd p)))

-- fillPath : {P : Int → Set}(ρ : isFib P)(x : P O) → _~~_ {P} x (fst (ρ O' id cofFalse ∅-elim (x , λ ())))
-- fillPath ρ x =
--   let filler = fill O' ρ id cofFalse ∅-elim x (λ ()) in
--   fst filler , snd (snd filler) , fillAtEnd O' ρ id cofFalse ∅-elim x (λ ())

-- fillPath' : {P : Int → Set}(ρ : isFib P)(x : P I) → _~~_ {P} (fst (ρ I' id cofFalse ∅-elim (x , λ ()))) x
-- fillPath' ρ x =
--   let filler = fill I' ρ id cofFalse ∅-elim x (λ ()) in
--   fst filler , fillAtEnd I' ρ id cofFalse ∅-elim x (λ ()) , snd (snd filler)


Path : ∀{ℓ}{Γ : Set ℓ}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Path A (x , (a , a')) = a ~ a'

reflPath : {Γ : Set}{A : Γ → Set}{x : Γ}(a : A x) → Path A (x , (a , a))
reflPath a = ((λ _ → a) , refl , refl)

reflPath' : {A : Set}{a a' : A} → (a ≡ a') → a ~ a'
reflPath' {A} {a} {a'} p = ((λ _ → a) , (refl , p))

reflPathEval : {A : Set}{a a' : A}(p : a ≡ a')(i : Int) → fst (reflPath' p) i ≡ a'
reflPathEval refl i = refl

PathExt : {A : Set}{a a' : A}{p q : a ~ a'} → fst p ≡ fst q → p ≡ q
PathExt refl = Σext refl (Σext uipImp uipImp)

FibPath : ∀{ℓ}{Γ : Set ℓ}{A : Γ → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
FibPath {A = A} α S p r s sh φ f (path₀ , extends₀) =
  (path₁ , (extends₁ , trivial))
  where
  f' : Int → [ φ ] → Π (Loc S) (A ∘ fst ∘ p)
  f' i u j = fst (f u j) i

  f₀ : (i : Int)
    → ⟦ g ∈ (prf (i ≈ O or i ≈ I) → Π (Loc S) (A ∘ fst ∘ p)) ∣ (φ , f' i) ⌣ (cofFace i O' ∨ cofFace i I' , g) ⟧
  fst (f₀ i) =
    ∨-rec (cofFace i O') (cofFace i I')
      (λ _ j → fst (snd (p j)))
      (λ _ j → snd (snd (p j)))
      (λ u v → ∅-elim (O≠I ( trans v (symm u))))
  snd (f₀ i) u =
    or-elim _
      (λ _ → uip)
      (λ i≡O → funext (λ j → trans (fst (snd (f u j))) (cong (fst (f u j)) i≡O)))
      (λ i≡I → funext (λ j → trans (snd (snd (f u j))) (cong (fst (f u j)) i≡I)))

  f₀' : (i : Int) → [ φ ∨ (cofFace i O' ∨ cofFace i I') ] → Π (Loc S) (A ∘ fst ∘ p)
  f₀' i = _∪_ {φ = φ} {ψ = cofFace i O' ∨ cofFace i I'} (f' i) (fst (f₀ i)) {p = snd (f₀ i)}

  extends₁' : (i : Int) → prf (((φ ∨ cofFace i O' ∨ cofFace i I') , f₀' i) ∙ r ↗ fst path₀ i)
  extends₁' i =
    or-elim-eq (λ v → f₀' i v r)
      (fst path₀ i)
      (λ u → cong (λ q → fst q i) (extends₀ u))
      (or-elim-eq (λ v → f₀' i ∣ inr v ∣ r)
        (fst path₀ i)
        (λ i≡O → symm (trans (fst (snd path₀)) (cong (fst path₀) i≡O)))
        (λ i≡I → symm (trans (snd (snd path₀)) (cong (fst path₀) i≡I))))

  comp : (i : Int) →
    ⟦ a ∈ ((A ∘ fst ∘ p) s)
    ∣ ((φ ∨ cofFace i O' ∨ cofFace i I') , f₀' i) ∙ s ↗ a
      & (All eq ∈ (r ≡ s) , subst (A ∘ fst ∘ p) eq (fst path₀ i) ≈ a) ⟧
  comp i = α S (fst ∘ p) r s sh (φ ∨ cofFace i O' ∨ cofFace i I') (f₀' i) (fst path₀ i , extends₁' i)

  path₁ : (Path A ∘ p) s
  fst path₁ i = fst (comp i)
  fst (snd path₁) = symm (fst (snd (comp O)) ∣ inr ∣ inl refl ∣ ∣)
  snd (snd path₁) = symm (fst (snd (comp I)) ∣ inr ∣ inr refl ∣ ∣)

  extends₁ : prf ((φ , f) ∙ s ↗ path₁)
  extends₁ u = PathExt (funext (λ i → fst (snd (comp i)) ∣ inl u ∣))

  trivial : (eq : r ≡ s) → subst (Path A ∘ p) eq path₀ ≡ path₁
  trivial refl = PathExt (funext (λ i → snd (snd (comp i)) refl))

FibPath' :
  {Γ : Set}
  (A : Fib Γ)
  → -----------
  Fib (Σ x ∈ Γ , fst A x × fst A x)
FibPath' (A , α) = (Path A , FibPath {A = A} α)

funextPath : {A : Set}{B : A → Set}{f g : (x : A) → B x} → ((a : A) → f a ~ g a) → f ~ g
fst (funextPath pointwise) i a = fst (pointwise a) i
fst (snd (funextPath pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (funextPath pointwise)) = funext (λ a → snd (snd (pointwise a)))

----------------------------------------------------------------------
-- Forming Path types is stable under reindexing
----------------------------------------------------------------------
reindexPath :
  {Δ Γ : Set}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Path A) (FibPath α) (ρ ×id) ≡ FibPath (reindex A α ρ)
reindexPath A α ρ = fibExt (Path A ∘ ρ ×id) (λ S p r s sh φ f x₁ → refl)
