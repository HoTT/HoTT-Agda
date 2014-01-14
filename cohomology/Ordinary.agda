{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.KGn
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Exactness

module cohomology.Ordinary {i} (G : Group i) (G-abelian : is-abelian G) where

open KGnExplicit G G-abelian

{- Definition of cohomology group C -}
module _ {j} (n : ℕ) (X : Ptd j) where
  {- Ordinary cohomology group -}
  C : Group (lmax i j)
  C = →Ω-Group X (Ptd-KG (S n))

  {- Underlying space of cohomology group -}
  CEl : Type (lmax i j)
  CEl = Group.El C -- Ptd-Trunc ⟨0⟩ (fst (X ∙→ Ptd-Ω (Ptd-KG (S n))))

  {- Basepoint of underlying space -}
  Cid : CEl
  Cid = GroupStructure.ident (Group.group-struct C)

  {- Underlying pointed space of cohomology group -}
  Ptd-CEl : Ptd (lmax i j)
  Ptd-CEl = ∙[ Group.El C , Cid ]

  {- Untruncated versions of the cohomology spaces -}
  uCEl : Type (lmax i j) -- CEl ≡ Trunc ⟨0⟩ uCEl
  uCEl = fst (X ∙→ Ptd-Ω (Ptd-KG (S n)))

  Ptd-uCEl : Ptd (lmax i j)
  Ptd-uCEl = X ∙→ Ptd-Ω (Ptd-KG (S n))

{- CF, the functorial action of C:
 - contravariant functor from pointed spaces to abelian groups -}
module _ {j k} (n : ℕ) {X : Ptd j} {Y : Ptd k} where

  {- untruncated version - from pointed spaces to pointed spaces -}
  uCF : fst (X ∙→ Y) → fst (Ptd-uCEl n Y ∙→ Ptd-uCEl n X)
  uCF (f , fpt) = 
    (λ {(g , gpt) → (g ∘ f , ap g fpt ∙ gpt)}) ,
    pair= idp (∙-unit-r _ ∙ ap-cst idp fpt)

  CF : fst (X ∙→ Y) → fst (Ptd-CEl n Y ∙→ Ptd-CEl n X)
  CF F = (Trunc-fmap (fst (uCF F)) , ap [_] (snd (uCF F)))

  CF-hom : fst (X ∙→ Y) → GroupHom (C n Y) (C n X)
  CF-hom (f , fpt) = record {
    f = T;
    pres-ident = ap [_] (snd (uCF (f , fpt)));
    pres-comp = λ G H → Trunc-elim 
      {B = λ G → ∀ H → T (G ⊕ H) == T G ⊗ T H}
      (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
      (λ {(g , gpt) → Trunc-elim
        {B = λ H → T ([ g , gpt ] ⊕ H) == T [ g , gpt ] ⊗ T H}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ {(h , hpt) → ap [_] (comp-lemma g h gpt hpt)})}) 
      G H}
    where
    _⊗_ = GroupStructure.comp (Group.group-struct (C n X))
    _⊕_ = GroupStructure.comp (Group.group-struct (C n Y))
    T = fst (CF (f , fpt))

    lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
      {a : A} {b : B} {c₁ c₂ : C}
      (f : A → B) (g h : B → C) (_⊙_ : C → C → C) 
      (fpt : f a == b) (gpt : g b == c₁) (hpt : h b == c₂)
      → ap (λ x → g x ⊙ h x) fpt ∙ ap2 _⊙_ gpt hpt
        == ap2 _⊙_ (ap g fpt ∙ gpt) (ap h fpt ∙ hpt)
    lemma f g h _⊙_ idp idp idp = idp

    comp-lemma : (g h : fst Y → Ω (Ptd-KG (S n))) 
      (gpt : g (snd Y) == idp) (hpt : h (snd Y) == idp) →
      Path {A = fst (X ∙→ Ptd-Ω (Ptd-KG (S n)))}
        ((λ x → g (f x) ∙ h (f x)) , ap (λ x → g x ∙ h x) fpt ∙ ap2 _∙_ gpt hpt)
        ((λ x → g (f x) ∙ h (f x)) , ap2 _∙_ (ap g fpt ∙ gpt) (ap h fpt ∙ hpt))
    comp-lemma g h gpt hpt = pair= idp (lemma f g h _∙_ fpt gpt hpt)

  {- TODO: prove that CF is actually a functor -}


{- Eilenberg-Steenrod Axioms -}

{- Suspension Axiom -}

C-Susp : ∀ {j} (n : ℕ) (X : Ptd j) → C (S n) (Ptd-Susp X) == C n X
C-Susp n X = SuspAdjointLoopIso.iso X (Ptd-KG (S (S n))) ∙ ap (→Ω-Group X) spec
  where
  spec : Ptd-Ω (Ptd-KG (S (S n))) == Ptd-KG (S n)
  spec = spectrum (S n)

{- Untruncated Exactness Axiom -}

{- pointed version of the function [cfcod] from lib.types.Cofiber -}
ptd-cfcod : ∀ {j k} {X : Ptd j} {Y : Ptd k} (F : fst (X ∙→ Y))
  → fst (Y ∙→ Ptd-Cof (fst F))
ptd-cfcod {X = X} (f , fpt) = 
  (cfcod f , ap (cfcod f) (! fpt) ∙ ! (cfglue f (snd X)))

module _ {j k} (n : ℕ) {X : Ptd j} {Y : Ptd k} where

  {- in image of (uCF n (ptd-cfcod F)) ⇒ in kernel of (uCF n F) -}
  uC-Exact-itok : (F : fst (X ∙→ Y)) 
    → is-exact-itok (uCF n (ptd-cfcod F)) (uCF n F)
  uC-Exact-itok (f , fpt) (g , gpt) = pair= 
    (λ= (λ x → ap g (! (cfglue f x)) ∙ gpt))
    (↓-app=cst-in $ 
      ap (g ∘ cfcod f) fpt 
      ∙ ap g (ap (cfcod f) (! fpt) ∙ ! (cfglue f (snd X))) ∙ gpt
        =⟨ lemma (cfcod f) g fpt (! (cfglue f (snd X))) gpt ⟩
      ap g (! (cfglue f (snd X))) ∙ gpt
        =⟨ ! (app=-β (λ x → ap g (! (cfglue f x)) ∙ gpt) (snd X)) ⟩
      app= (λ= (λ x → ap g (! (cfglue f x)) ∙ gpt)) (snd X)
        =⟨ ! (∙-unit-r _) ⟩
      app= (λ= (λ x → ap g (! (cfglue f x)) ∙ gpt)) (snd X) ∙ idp ∎)

    where
    {- path induction in place of simple but tedious algebraic manipulation -}
    lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} 
      {a₁ a₂ : A} {b : B} {c : C} (f : A → B) (g : B → C) 
      (p : a₁ == a₂) (q : f a₁ == b) (r : g b == c)
      → ap (g ∘ f) p ∙ ap g (ap f (! p) ∙ q) ∙ r == ap g q ∙ r
    lemma f g idp idp idp = idp

  {- in kernel of (uCF n F) ⇒ in image of (uCF n (ptd-cfcod F)) -}
  uC-Exact-ktoi : (F : fst (X ∙→ Y)) 
    → is-exact-ktoi (uCF n (ptd-cfcod F)) (uCF n F)
  uC-Exact-ktoi (f , fpt) (h , hpt) p = 
    (g , ! q ∙ hpt) , 
    pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (λ w → w ∙ hpt) (!-inv-r q))
    where 
    g = CofiberRec.f f idp h (! ∘ app= (ap fst p))
    q = ap g (snd (ptd-cfcod (f , fpt)))

    {- path induction in place of simple but tedious algebraic manipulation -}
    lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
      {a₁ a₂ : A} {b : B} (f : A → B) (g : B → C) 
      (p : a₁ == a₂) (q : b == f a₂)
      → ap g (ap f p ∙ ! q) == ap (g ∘ f) p ∙ ! (ap g q)
    lemma f g idp q = ap-! g q

{- Truncated Exactness Axiom -}

module _ {j k} (n : ℕ) {X : Ptd j} {Y : Ptd k} where

  {- in image of (CF n (ptd-cfcod F)) ⇒ in kernel of (CF n F) -}
  C-Exact-itok : (F : fst (X ∙→ Y)) 
    → is-exact-itok (CF n (ptd-cfcod F)) (CF n F)
  C-Exact-itok F = 
    Trunc-elim 
      {B = λ tG → fst (CF n F) (fst (CF n (ptd-cfcod F)) tG) == Cid n X}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ G → ap [_] (uC-Exact-itok n F G))

  {- in kernel of (CF n F) ⇒ merely in image of (CF n (ptd-cfcod F)) -}
  C-Exact-ktoi-mere : (F : fst (X ∙→ Y))
    → is-exact-ktoi-mere (CF n (ptd-cfcod F)) (CF n F)
  C-Exact-ktoi-mere F = 
    Trunc-elim
      {B = λ H → fst (CF n F) H == Cid n X
         → Trunc ⟨-1⟩ (Σ (CEl n (Ptd-Cof (fst F))) 
                         (λ K → fst (CF n (ptd-cfcod F)) K == H))}
      (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
      (λ H tp → Trunc-rec Trunc-level
        (λ p → [ (let wit = uC-Exact-ktoi n F H p  
                  in [ fst wit ] , (ap [_] (snd wit))) ])
        (–> (Trunc=-equiv _ _) tp))

