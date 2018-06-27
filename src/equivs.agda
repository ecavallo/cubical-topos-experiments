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
module equivs where 

open import prelude
open import hprop
open import logic
open import interval
open import shift
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Contr and Ext
----------------------------------------------------------------------
Contr' : Set → Set
Contr' A = Σ a₀ ∈ A , ((a : A) → a ~ a₀)

Contr : {Γ : Set} → (Γ → Set) → Set
Contr {Γ} A = (x : Γ) → Contr' (A x)

Ext' : Set → Set
Ext' A = (φ : Cof)(f : [ φ ] → A) → ⟦ a ∈ A ∣ (φ , f) ↗ a ⟧

Ext : {Γ : Set} → (Γ → Set) → Set
Ext {Γ} A = (x : Γ) → Ext' (A x)

contr2ext : {Γ : Set}{A : Γ → Set} → isFib A → Contr A → Ext A
contr2ext {Γ} {A} α ap x φ f = (fst a' , (λ u → trans (q u) (p u)))
  where
  a : A x
  a = fst (ap x)

  c : (a' : A x) → a' ~ a
  c = snd (ap x)

  path : [ φ ] → Int → A x
  path u = fst (c (f u))
  
  a' : ⟦ a' ∈ (A x) ∣ (φ , path) ∙ O ↗ a' & (All eq ∈ I ≡ O , subst (λ _ → A x) eq a ≈ a') ⟧
  a' = α int (λ _ → x) I O (cflip int O~>I) φ path (a , λ u → snd (snd (c (f u))))

  p : (u : [ φ ]) → f u ≡ fst (c (f u)) O
  p u = symm (fst (snd (c (f u))))

  q : (u : [ φ ]) → fst (c (f u)) O ≡ fst a'
  q = fst (snd a')

-- contr2extFalse : {Γ : Set}{A : Γ → Set}(α : isFib A)(c : Contr A)(x : Γ)
--   → fst (contr2ext α c x cof⊥ ∅-elim) ≡ fst (α I' (λ _ → x) cof⊥ ∅-elim (fst (c x) , (λ ())))
-- contr2extFalse {Γ} {A} α c x = 
--   proof:
--       fst (contr2ext α c x cof⊥ ∅-elim)
--     ≡[ cong (λ hh' → fst (α I' (λ _ → x) cof⊥ (fst hh') ((fst (c x)) , snd hh'))) equal ]≡
--       fst (α I' (λ _ → x) cof⊥ ∅-elim (fst (c x) , (λ ())))
--   qed
--     where
--       path : [ cof⊥ ] → Int → A x
--       path u = fst (snd (c x) (∅-elim u))
--       equal : _≡_ {A = Σ path ∈ ([ cof⊥ ] → Int → A x) , prf ((cof⊥ , path) ∙ I ↗ fst (c x))} (path , (λ u → snd (snd (snd (c x) (∅-elim u))))) (∅-elim , λ ())
--       equal = Σext (funext (λ ())) (funext (λ ()))


ext2fib : {Γ : Set}{A : Γ → Set} → Ext A → isFib A × Contr A
fst (ext2fib {A = A} ext) S p r s sh φ f a =
  fst a' ,
  (λ u → snd a' ∣ inl u ∣) ,
  (λ eq → snd a' ∣ inr eq ∣)
  where
  φ' : Cof
  φ' = φ ∨ cofCShift S sh

  f' : [ φ' ] → A (p s)
  f' = ∨-rec φ (cofCShift S sh)
    (λ u → f u s)
    (λ eq → subst (A ∘ p) eq (fst a))
    (λ {u refl → snd a u})

  a' = ext (p s) φ' f'
fst (snd (ext2fib ext) x) = fst (ext x cof⊥ ∅-elim)
snd (snd (ext2fib {A = A} ext) x) a =
  (λ i → fst (path i)) ,
  symm (snd (path O) ∣ inl refl ∣) ,
  symm (snd (path I) ∣ inr refl ∣)
  where
  ends : (i : Int) → prf (i ≈ O or i ≈ I) → A x
  ends i = OI-elim (λ {(inl refl) → a; (inr refl) → fst (ext x cof⊥ ∅-elim)})

  path : (i : Int) → ⟦ a' ∈ A x ∣ (cofFace i O' ∨ cofFace i I' , ends i) ↗ a' ⟧
  path = λ i → ext x (cofFace i O' ∨ cofFace i I') (ends i)

----------------------------------------------------------------------
-- Equivalences and quasi-inverses
----------------------------------------------------------------------
Fiber : {A B : Set}(f : A → B)(b : B) → Set
Fiber {A} f b = Σ a ∈ A , f a ~ b

Equiv' : {A B : Set}(f : A → B) → Set
Equiv' {A} {B} f = (b : B) → Contr' (Fiber f b)

Equiv : {Γ : Set}{A B : Γ → Set}(f : (x : Γ) → A x → B x) → Set
Equiv {Γ} f = (x : Γ) → Equiv' (f x)

Qinv : {A B : Set}(f : A → B) → Set
Qinv {A} {B} f = Σ g ∈ (B → A) , ((b : B) → f (g b) ~ b) × ((a : A) → g (f a) ~ a)

fiberext : {A B : Set}{f : A → B}{b : B}{x y : Fiber f b} → fst x ≡ fst y → fst (snd x) ≡ fst (snd y) → x ≡ y
fiberext refl refl = Σext refl (PathExt refl)

-- Singletons are contractible
Sing' : {A : Set} → A → Set
Sing' {A} a = Σ a' ∈ A , (a' ~ a)

Sing : {Γ : Set}(A : Γ → Set) → (Σ Γ A → Set)
Sing A (γ , a) = Sing' a

singExt : {A : Set}{a : A}{s s' : Sing' a} → fst (snd s) ≡ fst (snd s') → s ≡ s'
singExt {s = (_ , _ , refl , refl)} {s' = (_ , _ , refl , refl)} refl = refl

singContr : {Γ : Set}{A : Γ → Set} → isFib A → Contr (Sing A)
fst (singContr {A = A} α (γ , a)) = a , reflPath' refl
snd (singContr {A = A} α (γ , a)) (a' , p) =
  (λ i → fst (square i O) ,
         ((λ j → fst (square i j)) ,
          refl ,
          symm (snd (snd (square i I)) refl))) ,
  singExt (funext (λ j → symm (fst (snd (square O j)) ∣ inl refl ∣))) ,
  singExt (funext (λ j → symm (fst (snd (square I j)) ∣ inr refl ∣)))

  where
  ends : (i : Int) → prf (i ≈ O or i ≈ I) → Int → A γ
  ends i = OI-elim (λ {(inl refl) → fst p; (inr refl) → λ _ → a})

  square : (i j : Int)
    → ⟦ b ∈ A γ ∣ (cofFace i O' ∨ cofFace i I' , ends i) ∙ j ↗ b
                  & (All eq ∈ (I ≡ j) , subst (λ _ → A γ) eq a ≈ b) ⟧
  square i j =
    compToFill int _ (α int (λ _ → γ)) I j (shiftCompToFill int (cflip int O~>I) j)
      (cofFace i O' ∨ cofFace i I')
      (ends i)
      (a , 
       OI-elim-dep λ {(inl refl) → snd (snd p); (inr refl) → refl})

-- The identity map at a fibration is an equivalence
idEquiv : {Γ : Set}{A : Γ → Set} → isFib A → Equiv {A = A} (λ _ a → a)
idEquiv α γ a = singContr α (γ , a)

-- -- This is a standard result in HoTT.
-- postulate
--  qinv2equiv :
--   {Γ : Set}{A B : Γ → Set}(α : isFib A)(β : isFib B)
--   (f : (x : Γ) → A x → B x) → ((x : Γ) → Qinv (f x)) → Equiv f

