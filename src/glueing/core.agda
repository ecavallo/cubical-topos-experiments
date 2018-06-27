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
module glueing.core where 

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
-- Glueing
----------------------------------------------------------------------
res : ∀{ℓ}(Γ : Set ℓ)(Φ : Γ → Cof) → Set ℓ
res Γ Φ = Σ x ∈ Γ , [ Φ x ]

<_,id> : ∀{ℓ}{Γ : Set ℓ} → Γ → Int → Γ × Int
< x ,id> i = (x , i)

i=OI : ∀{ℓ}{Γ : Set ℓ} → Γ × Int → Cof
i=OI (x , i) = (cofFace i O') ∨ (cofFace i I')

Glue : ∀{ℓ}
  {Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  Γ → Set
Glue Φ A B f x = Σ a ∈ ((u : [ Φ x ]) → A (x , u)) , ⟦ b ∈ (B x) ∣ All u ∈ [ Φ x ] , f x u (a u) ≈ b ⟧

glue : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (xu : res Γ Φ) → A xu → Glue Φ A B f (fst xu)
glue {Γ = Γ} {Φ} {A} {B} f (x , u) a =
  ((λ v → moveA v a) , (f x u a , (λ v → cong (λ{(u , a) → f x u a}) (symm (moveMove v)))))
  where
  moveA : (v : [ Φ x ]) → A (x , u) → A (x , v)
  moveA v = subst (λ v → A (x , v)) (eq [ Φ x ]ᴾ)
  moveMove : (v : [ Φ x ]) → (u , a) ≡ (v , moveA v a)
  moveMove v = Σext (eq [ Φ x ]ᴾ) refl

unglue : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → Glue Φ A B f x → B x
unglue _ _ (_ , b , _) = b

unglue' : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ)(u : [ Φ x ]) → Glue Φ A B f x → A (x , u)
unglue' _ _ u (a , _ , _) = a u

unglueGlue : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (xu : res Γ Φ) → (unglue {Φ = Φ} f (fst xu)) ∘ (glue {Φ = Φ} f xu) ≡ f (fst xu) (snd xu)
unglueGlue f (x , u) = funext (λ a → refl)

glue' : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (a : (u : [ Φ x ]) → A (x , u))
  → ⟦ b ∈ B x ∣ All u ∈ [ Φ x ] , f x u (a u) ≈ b ⟧ → Glue Φ A B f x
glue' f x a (b , bPrf) = (a , b , bPrf)

unglueGlue' : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (a : (u : [ Φ x ]) → A (x , u))
   → (unglue {Φ = Φ} f x) ∘ (glue' {Φ = Φ} f x a) ≡ fst
unglueGlue' f x a = refl

glueUnglue : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (g : Glue Φ A B f x)
   → glue' {Φ = Φ} f x (fst g) (unglue {Φ = Φ} f x g , snd (snd g)) ≡ g
glueUnglue f x g = refl

glueExt : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  {x : Γ}
  (g g' : Glue Φ A B f x)
  (p : fst g ≡ fst g')
  (q : fst (snd g) ≡ fst (snd g'))
  → ---------------
  g ≡ g'
glueExt _ (_ , _ , fa≡b) (_ , _ , fa≡b') refl refl =
  Σext refl (Σext refl (funext (λ u → uip (fa≡b u) (fa≡b' u))))

-- The fibration structure that we get for the fiber of f
-- regarded as a family over B
σ : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : Fib (res Γ Φ)}
  {B : Fib Γ}
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (x : Γ)
  (u : [ Φ x ])
  → ---------------
  isFib (Fiber (f x u))
σ {Γ = Γ} {Φ} {A , α} {B , β} f x u =
  FibΣ {B = λ{ (b , a) → f x u a ~ b}}
    (reindex A α (λ _ → x , u))
    (reindex (Path B) (FibPath β) (λ{ (b , a) → (x , f x u a , b)}))

FibGlue : ∀{ℓ}
  {Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (Glue Φ A B f)
FibGlue {Γ = Γ} {Φ} {A} {B} f equiv α β S p r s sh ψ q ((a , b , fa↗b) , ext) =
  (g₁ , ext' , trivial')
  where
  x : Γ
  x = p s

  ~a : [ ψ ] → (u : [ Φ x ]) → A (x , u)
  ~a v = fst (q v s)
  ~b : [ ψ ] → B x
  ~b v = fst (snd (q v s))
  f~a=~b : (v : [ ψ ])(u : [ Φ x ]) → f x u (~a v u) ≡ ~b v
  f~a=~b v = snd (snd (q v s))
  
  qb : [ ψ ] → Π (Loc S) (B ∘ p)
  qb v i = fst (snd (q v i))

  b₁' : (i : Loc S) → ⟦ b' ∈ (B (p i)) ∣ (ψ , qb) ∙ i ↗ b' & (All eq ∈ r ≡ i , subst (B ∘ p) eq b ≈ b') ⟧
  b₁' i =
    compToFill S (B ∘ p) (β S p) r i (shiftCompToFill S sh i) ψ qb (b , (λ u → cong (λ g → fst (snd g)) (ext u)))

  a₁'p' : (u : [ Φ x ])(v : [ ψ ]) → Fiber (f x u) (fst (b₁' s))
  a₁'p' u v = (~a v u , reflPath' (trans (fst (snd (b₁' s)) v) (f~a=~b v u)))

  a₁'p'-∪-arefl : (u : [ Φ x ])(v : [ ψ ∨ cofCShift S sh ])
    → Fiber (f x u) (fst (b₁' s))
  a₁'p'-∪-arefl u =
    ∨-rec ψ (cofCShift S sh)
      (a₁'p' u)
      (λ {refl → (a u , reflPath' (trans (snd (snd (b₁' r)) refl) (fa↗b u)))})
      (λ {v refl →
        Σext (cong (λ h → (fst h) u) (ext v))
             (congindexed (λ _ → reflPath')
               (cong (λ h → fst h u) (ext v))
               (uip _ _))})

  ε : (u : [ Φ x ]) → Ext' (Fiber (f x u) (fst (b₁' s)))
  ε u = contr2ext (σ {Φ = Φ} {A , α} {B , β} f x u) (equiv x u) (fst (b₁' s))

  a₁p : (u : [ Φ x ]) → ⟦ ap ∈ Fiber (f x u) (fst (b₁' s)) ∣ (ψ ∨ cofCShift S sh , a₁'p'-∪-arefl u) ↗ ap ⟧
  a₁p u = ε u (ψ ∨ cofCShift S sh) (a₁'p'-∪-arefl u)

  a₁ : ⟦ a₁ ∈ ((u : [ Φ x ]) → A (x , u)) ∣ (ψ , λ v → ~a v) ↗ a₁ ⟧
  a₁ =
    (λ u → fst (fst (a₁p u))) ,
    (λ v → (funext (λ u → cong fst (snd (a₁p u) ∣ inl v ∣))))

  a₁trivial : (eq : r ≡ s) → subst (λ i → (u : [ Φ (p i) ]) → A (p i , u)) eq a ≡ fst a₁
  a₁trivial refl = funext (λ u → cong fst (snd (a₁p u) ∣ inr refl ∣))

  ~b-∪-fa₁ : [ ψ ∨ Φ x ] → Int → B (p s)
  ~b-∪-fa₁ u i =
    ∨-rec ψ (Φ x)
      ~b
      (λ u → fst (snd (fst (a₁p u))) i)
      agree
      u
    where
    agree : prf ((ψ , ~b) ⌣ (Φ x , (λ u → fst (snd (fst (a₁p u))) i)))
    agree v u =
      let p≡refl = cong (λ ap → fst (snd ap) i) (snd (a₁p u) ∣ inl v ∣) in
      let refl≡ = reflPathEval ((trans (fst (snd (b₁' s)) v) (f~a=~b v u))) i in
      trans p≡refl (trans (symm refl≡) (fst (snd (b₁' s)) v))

  ~b-∪-fa₁-∪-b : [ (ψ ∨ Φ x) ∨ (cofCShift S sh) ] → Int → B (p s)
  ~b-∪-fa₁-∪-b w i =
    ∨-rec (ψ ∨ Φ x) (cofCShift S sh)
      (λ u → ~b-∪-fa₁ u i)
      (λ {refl → b})
      (λ {w' refl →
        or-elim-eq (λ w → ~b-∪-fa₁ w i) b
          (λ v → cong (λ tr → fst (snd tr)) (ext v))
          (λ u → trans (fa↗b u) (cong (λ tr → fst (snd tr) i) (symm (snd (a₁p u) ∣ inr refl ∣))))
          w'})
      w

  b₁ : ⟦ b₁ ∈ (B x) ∣ ((ψ ∨ Φ x) ∨ (cofCShift S sh) , ~b-∪-fa₁-∪-b) ∙ O ↗ b₁
                     & (All eq ∈ (I ≡ O) , subst (λ _ → B x) eq (fst (b₁' s)) ≈ b₁) ⟧
  b₁ =
    β int (λ _ → x) I O (cflip int O~>I) ((ψ ∨ Φ x) ∨ (cofCShift S sh)) ~b-∪-fa₁-∪-b
      (fst (b₁' s) ,
       or-elim-eq (λ w → ~b-∪-fa₁-∪-b w I)
         (fst (b₁' s))
         (or-elim-eq (λ w → ~b-∪-fa₁ w I)
           (fst (b₁' s))
           (fst (snd (b₁' s)))
           (λ u → snd (snd (snd (fst (a₁p u))))))
         λ {refl → snd (snd (b₁' r)) refl})

  g₁ : Glue Φ A B f x
  g₁ = (fst a₁ , fst b₁ , (λ u → trans (fst (snd b₁) ∣ inl ∣ inr u ∣ ∣) (symm (fst (snd (snd (fst (a₁p u))))))))

  ext' : prf ((ψ , q) ∙ s ↗ g₁)
  ext' v = glueExt {Φ = Φ} f (q v s) g₁ (snd a₁ v) (fst (snd b₁) ∣ inl ∣ inl v ∣ ∣)

  trivial' : (eq : r ≡ s) → subst (Glue Φ A B f ∘ p) eq (a , b , fa↗b) ≡ g₁
  trivial' refl =
    cong (λ {((a , b) , eq) → (a , b , eq)})
      (Σext
        (×ext
          (funext (λ u → cong fst (snd (a₁p u) ∣ inr refl ∣)))
          (fst (snd b₁) ∣ inr refl ∣))
        (funext (λ u → uip _ _)))

GlueFib :
  {Γ : Set}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  Fib Γ
GlueFib Φ (A , α) (B , β) f equiv = (Glue Φ A B f , FibGlue {Φ = Φ} f equiv α β)

-- fstσFalse :
--   {Γ : Set}
--   (A : Fib (res (Γ × Int) i=OI))
--   (B : Fib (Γ × Int))
--   (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
--   (x : Γ)
--   (b : fst B (x , I))
--   → ---------------
--   fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f (x , I) ∣ inr refl ∣) (equiv (x , I) ∣ inr refl ∣) b cof⊥ ∅-elim))
--     ≡ trivComp A I' ((x , I) , ∣ inr refl ∣) (fst (fst (equiv (x , I) ∣ inr refl ∣ b)))
-- abstract
--  fstσFalse A B f equiv x b =

--   proof:
  
--       fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f xI u) ctrFib b cofFalse ∅-elim))
    
--     ≡[ cong fst (contr2extFalse (σ {Φ = i=OI} {A} {B} f xI u) ctrFib b) ]≡
      
--       fst (trivComp (Fiber (f xI u) , σ {Φ = i=OI} {A} {B} f xI u) I' b (fst (ctrFib b)))
    
--     ≡[ fstFibΣid
--          (reindex (fst A) (snd A) (λ _ → xI , u))
--          (reindex (Path (fst B)) (FibPath (snd B)) (λ{ (_ , a) → (xI , f xI u a , b)}))
--          I' id cofFalse ∅-elim (fst (equiv (x , I) ∣ inr refl ∣ b) , (λ ()))
--       ]≡
       
--       fst (snd A I' (λ _ → xI , u) cofFalse h (fst (fst (ctrFib b)) , h'))
    
--     ≡[ cong (λ hh' →
--          fst (snd A I' (λ _ → xI , u) cofFalse (fst hh') ((fst (fst (ctrFib b))) , (snd hh'))))
--            (Σext (funext (λ ())) (funext (λ ())))
--       ]≡
      
--       trivComp A I' ((x , I) , ∣ inr refl ∣) (fst (fst (equiv (x , I) ∣ inr refl ∣ b)))
    
--   qed
  
--     where
    
--       xI = (x , I)
--       u : [ i=OI xI ]
--       u = ∣ inr refl ∣
--       ctrFib : Contr (Fiber (f xI u))
--       ctrFib = equiv xI u
      
--       h : ∅ → Int → fst A (xI , u)
--       h = λ u i → fst (∅-elim {A = Int → Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} u i)
--       hb : (u : ∅)(i : Int) → f (x , I) ∣ inr refl ∣ (h u i) ~ b
--       hb = λ u i → snd (∅-elim {A = Int → Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} u i)
--       h'' : (u : ∅) → ((h u I) , hb u I) ≡ fst (equiv (x , I) ∣ inr refl ∣ b)
--       h'' = λ ()
--       h' : (u : ∅) → h u I ≡ fst (fst (equiv (x , I) ∣ inr refl ∣ b))
--       h' = λ u → cong {A = Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} fst (h'' u)

-- -- Given a fibration over Γ × Int we can compose from (x,O) to (x,I)
-- compOI  :
--   {Γ : Set}
--   (B : Fib (Γ × Int))
--   (x : Γ)
--   (b : fst B (x , O))
--   →
--   fst B (x , I)
-- compOI (_ , β) x b = fst (β O' < x ,id> cofFalse ∅-elim (b , λ ()))

-- -- Just convincing Agda that a series of maps ∅ → X are all equal. Final result is:
-- --
-- -- unglue (compOI-in-Glue (glue a)) ≡ fst (empty extension of (compOI-in-B (f a)))
-- --
-- uaβhelper3' :
--   {Γ : Set}
--   (A : Fib (res (Γ × Int) i=OI))
--   (B : Fib (Γ × Int))
--   (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
--   (x : Γ)
--   (a : fst A ((x , O) , ∣ inl refl ∣))
--   → ---------------
--   unglue' {Φ = i=OI} f (x , I) ∣ inr refl ∣
--     (compOI (GlueFib i=OI A B f equiv) x
--       (glue {Φ = i=OI} f (((x , O) , ∣ inl refl ∣))  a))
--     ≡ fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f (x , I) ∣ inr refl ∣) (equiv (x , I) ∣ inr refl ∣)
--        (compOI B x (f (x , O) ∣ inl refl ∣ a)) cofFalse ∅-elim))
-- abstract
--  uaβhelper3' {Γ} (A , α) (B , β) f e x a =
--    cong (λ hs → fst (fst (contr2ext (σ {Φ = i=OI} {A , α} {B , β} f (x , I) ∣ inr refl ∣) (e (x , I) ∣ inr refl ∣)
--      (fst (β O' < x ,id> cofFalse (fst hs) ((f (x , O) ∣ inl refl ∣ a) , (fst (snd hs)))))
--      cofFalse (snd (snd hs))))) equal
--   where
--   ~a : [ cofFalse ] → (u : [ i=OI (x , I) ]) → A ((x , I) , u)
--   ~a v = fst (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I)
--   ~b : [ cofFalse ] → B (x , I)
--   ~b v = fst (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I))
--   f~a=~b : (v : [ cofFalse ])(u : [ i=OI (x , I) ]) → f (x , I) u (~a v u) ≡ ~b v
--   f~a=~b v = snd (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I))
  
--   qb : [ cofFalse ] → Π (B ∘ < x ,id>)
--   qb u i = fst (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} u i))

--   h'' : (u : ∅) → (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} u O) ≡ (glue {Φ = i=OI} f ((x , O) , ∣ inl refl ∣) a)
--   h'' = λ ()
--   h' : prf ((cofFalse , qb) ∙ O ↗ (f (x , O) ∣ inl refl ∣ a))
--   h' = λ u → cong (λ g → fst (snd g)) (h'' u)
  
--   b₁' : ⟦ b ∈ (B (x , I)) ∣ (cofFalse , qb) ∙ I ↗ b ⟧
--   b₁' = β O' < x ,id> cofFalse qb (f (x , O) ∣ inl refl ∣  a , h')

--   a₁'p' : (v : [ cofFalse ]) → Fiber (f (x , I) ∣ inr refl ∣) (fst b₁')
--   a₁'p' v = (~a v ∣ inr refl ∣ , reflPath' (trans (snd b₁' v) (f~a=~b v ∣ inr refl ∣)))
--   equal : _≡_ {A = Σ qb ∈ ([ cofFalse ] → Π (B ∘ < x ,id>)) , Σ h' ∈ (prf ((cofFalse , qb) ∙ O ↗ (f (x , O) ∣ inl refl ∣ a))) , (∅ →
--     Fiber (f (x , I) ∣ inr refl ∣) (fst (β O' < x ,id> cofFalse qb (f (x , O) ∣ inl refl ∣ a , h'))))} (qb , h' , a₁'p') (∅-elim , (λ ()) , ∅-elim)
--   equal = Σext (funext (λ ())) (Σext (funext (λ ())) (funext (λ ())))

-- -- Composing from O to I in Glue i=OI is equal to a trivial comp
-- -- from the f^-1 applied to a comp through B. In the end f^-1
-- -- will be id and the inner comp will also be trivial.
-- --
-- -- unglue (compOI-in-Glue (glue a)) ≡ trivComp (f^-1 (compOI-in-B (f a)))
-- --
-- uaβhelper3 :
--   {Γ : Set}
--   (A : Fib (res (Γ × Int) i=OI))
--   (B : Fib (Γ × Int))
--   (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
--   (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
--   (x : Γ)
--   (a : fst A ((x , O) , ∣ inl refl ∣))
--   → ---------------
--   unglue' {Φ = i=OI} f (x , I) ∣ inr refl ∣
--     (compOI (GlueFib i=OI A B f equiv) x
--       (glue {Φ = i=OI} f (((x , O) , ∣ inl refl ∣))  a))
--     ≡ fst ((snd A) I' (λ _ → (x , I) , ∣ inr refl ∣) cofFalse ∅-elim
--         (fst (fst (equiv (x , I) ∣ inr refl ∣ (compOI B x (f (x , O) ∣ inl refl ∣ a)))), λ ()))
-- abstract
--  uaβhelper3 A B f equiv x a =
--   trans
--     (fstσFalse A B f equiv x
--       (fst (snd B O' < x ,id> cofFalse ∅-elim ((f (x , O) ∣ inl refl ∣ a) , (λ ())))))
--     (uaβhelper3' A B f equiv x a)
