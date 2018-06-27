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
module glueing.fixcore where 

open import glueing.core
open import glueing.strict

open import prelude
open import hprop
open import logic
open import interval
open import cof
open import shift
open import fibrations
open import equivs
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Fixing the composition
----------------------------------------------------------------------

abstract
 FibFix : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {G : Γ → Set}
  → ---------------
  (α : isFib {Γ = res Γ Φ} (G ∘ fst)) → isFib G → isFib G
 FibFix {Γ = Γ} {Φ} {G} α γ S p r s sh ψ f (g , ext) =
  let
    g' = γ S p r s sh (ψ ∨ cof∀ S (Φ ∘ p)) f' (g , ext')
  in
    (fst g') ,
    (λ u → fst (snd g') ∣ inl u ∣) ,
    λ {refl → snd (snd g') refl}
  where
  aFill : (∀iΦ : [ cof∀ S (Φ ∘ p) ]) (i : Loc S) →
    ⟦ a' ∈ G (p i) ∣ ((ψ , f) ∙ i ↗ a') & (All eq ∈ (r ≡ i) , subst (G ∘ p) eq g ≈ a') ⟧
  aFill ∀iΦ i =
    compToFill S (G ∘ p) (α S (λ i → p i , ∀iΦ i)) r i (shiftCompToFill S sh i) ψ f (g , ext)
  f' : [ ψ ∨ cof∀ S (Φ ∘ p) ] → Π (Loc S) (G ∘ p)
  f' = ∨-rec ψ (cof∀ S (Φ ∘ p))
         f
         (λ u i → fst (aFill u i))
         (λ v ∀Φi → funext (λ i → fst (snd (aFill ∀Φi i)) v))
  ext' : prf ((ψ ∨ cof∀ S (Φ ∘ p) , f') ∙ r ↗ g)
  ext' = or-elim-eq (λ u → f' u r) g (λ u → ext u) (λ ∀iΦ → symm (snd (snd (aFill ∀iΦ r)) refl))

 isFixed : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {G : Γ → Set}
  (α : isFib {Γ = res Γ Φ} (G ∘ fst))
  (γ : isFib G)
  → ---------------
  reindex G (FibFix {Φ = Φ} {G} α γ) fst ≡ α
 isFixed {Γ = Γ} {Φ} {G} α γ =
   fibExt (G ∘ fst) calc
   where
  calc : (S : Shape) (p : Loc S → Σ Γ (λ x → [ Φ x ])) (r s : Loc S) (sh : prf (S ∋ r ~> s)) (ψ : Cof)
      (f : [ ψ ] → Π (Loc S) (G ∘ fst ∘ p))
      (a₀ : set (G (fst (p r))) (_↗_ ((ψ , f) ∙ r))) →
      fst (reindex G (FibFix {Γ = Γ} {Φ} {G} α γ) fst S p r s sh ψ f a₀) ≡ fst (α S p r s sh ψ f a₀)
  calc S p r s sh ψ f (g , ext) =
    symm (fst (snd (γ S p' r s sh (ψ ∨ cof∀ S (Φ ∘ p')) f' (g , ext'))) ∣ inr (λ i → snd (p i)) ∣)
    where
    p' : Loc S → Γ
    p' i = fst (p i)

    aFill : (∀iΦ : [ cof∀ S (Φ ∘ p') ]) (i : Loc S) →
      ⟦ a' ∈ G (p' i) ∣ ((ψ , f) ∙ i ↗ a') & (All eq ∈ (r ≡ i) , subst (G ∘ p') eq g ≈ a') ⟧
    aFill ∀iΦ i =
      compToFill S (G ∘ p') (α S (λ i → p' i , ∀iΦ i)) r i (shiftCompToFill S sh i) ψ f (g , ext)
    f' : [ ψ ∨ cof∀ S (Φ ∘ p') ] → Π (Loc S) (G ∘ p')
    f' = ∨-rec ψ (cof∀ S (Φ ∘ p'))
           f
           (λ u i → fst (aFill u i))
           (λ v ∀Φi → funext (λ i → fst (snd (aFill ∀Φi i)) v))
    ext' : prf ((ψ ∨ cof∀ S (Φ ∘ p') , f') ∙ r ↗ g)
    ext' = or-elim-eq (λ u → f' u r) g (λ u → ext u) (λ ∀iΦ → symm (snd (snd (aFill ∀iΦ r)) refl))

 sameOtherwise : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {G : Γ → Set}
  (α : isFib {Γ = res Γ Φ} (G ∘ fst))
  (γ : isFib G)
  (S : Shape)
  (p : Loc S → Γ)
  (¬∀Φ : [ cof∀ S (Φ ∘ p) ] → ∅)
  → ---------------
  FibFix {Γ = Γ} {Φ} {G} α γ S p ≡ γ S p
 sameOtherwise {Γ = Γ} {Φ} {G} α γ S p ¬∀Φ =
   fibExt' G {α = FibFix {Φ = Φ} {G} α γ} {α' = γ} S p calc
   where
   calc : (r s : Loc S) (sh : prf (S ∋ r ~> s)) (ψ : Cof) (f : [ ψ ] → Π (Loc S) (G ∘ p))
     (a₀ : set (G (p r)) (_↗_ ((ψ , f) ∙ r))) →
     fst (FibFix {Φ = Φ} {G} α γ S p r s sh ψ f a₀) ≡ fst (γ S p r s sh ψ f a₀)
   calc r s sh ψ f (g , ext) =
      proof:
          fst (γ S p r s sh (ψ ∨ cof∀ S (Φ ∘ p)) f' (g , ext'))
        ≡[ cong (λ ψfext → fst (γ S p r s sh (fst (fst ψfext)) (snd (fst ψfext)) (g , snd ψfext)) ) tripleEq ]≡
          fst (γ S p r s sh ψ f (g , ext))
      qed
     where
     aFill : (∀iΦ : [ cof∀ S (Φ ∘ p) ]) (i : Loc S) →
       ⟦ a' ∈ G (p i) ∣ ((ψ , f) ∙ i ↗ a') & (All eq ∈ (r ≡ i) , subst (G ∘ p) eq g ≈ a') ⟧
     aFill ∀iΦ i =
       compToFill S (G ∘ p) (α S (λ i → p i , ∀iΦ i)) r i (shiftCompToFill S sh i) ψ f (g , ext)
     f' : [ ψ ∨ cof∀ S (Φ ∘ p) ] → Π (Loc S) (G ∘ p)
     f' = ∨-rec ψ (cof∀ S (Φ ∘ p))
            f
            (λ u i → fst (aFill u i))
            (λ v ∀Φi → funext (λ i → fst (snd (aFill ∀Φi i)) v))
     ext' : prf ((ψ ∨ cof∀ S (Φ ∘ p) , f') ∙ r ↗ g)
     ext' = or-elim-eq (λ u → f' u r) g (λ u → ext u) (λ ∀iΦ → symm (snd (snd (aFill ∀iΦ r)) refl))
     
     pairEq : _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → Π (Loc S) (G ∘ p))} (ψ ∨ cof∀ S (Φ ∘ p) , f') (ψ , f)
     pairEq = lemma propsEq
       (or-elim (λ u → f' u ≡ f (subst [_] propsEq u)) (λ u → uip)
         (λ u → cong f (eq [ ψ ]ᴾ)) (λ u → ∅-elim (¬∀Φ u)))
         where
         lemma : {X : Set}{ψ ψ' : Cof}{f : [ ψ ] → X}{f' : [ ψ' ] → X}
           (p : ψ ≡ ψ') → ((u : [ ψ ]) → f u ≡ f' (subst [_] p u))
           → _≡_ {A = Σ ψ ∈ Cof , ([ ψ ] → X)} (ψ , f) (ψ' , f')
         lemma refl eq = Σext refl (funext eq)

         propsEq : (ψ ∨ cof∀ S (Φ ∘ p)) ≡ ψ
         propsEq = cofExt
           (∨-rec ψ (cof∀ S (Φ ∘ p)) id (λ x → ∅-elim (¬∀Φ x)) (λ _ _ → eq [ ψ ]ᴾ))
           (λ x → ∣ inl x ∣)

     tripleEq : ((ψ ∨ cof∀ S (Φ ∘ p) , f') , ext') ≡ ((ψ , f) , ext)
     tripleEq = Σext pairEq (eq ((ψ , f) ∙ r ↗ g))
