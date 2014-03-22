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

  uCid : uCEl
  uCid = snd Ptd-uCEl

{- CF, the functorial action of C:
 - contravariant functor from pointed spaces to abelian groups -}
module _ {j k} (n : ℕ) {X : Ptd j} {Y : Ptd k} where

  {- untruncated version - from pointed spaces to pointed spaces -}
  uCF : fst (X ∙→ Y) → fst (Ptd-uCEl n Y ∙→ Ptd-uCEl n X)
  uCF F = 
    (λ {G → G ∘ptd F}) ,
    pair= idp (∙-unit-r _ ∙ ap-cst idp (snd F))

  CF : fst (X ∙→ Y) → fst (Ptd-CEl n Y ∙→ Ptd-CEl n X)
  CF F = (Trunc-fmap (fst (uCF F)) , ap [_] (snd (uCF F)))

  CF-hom : fst (X ∙→ Y) → GroupHom (C n Y) (C n X)
  CF-hom (f , fpt) = record {
    f = T;
    pres-ident = ap [_] (snd (uCF (f , fpt)));
    pres-comp = λ G H → Trunc-elim 
      {B = λ G → ∀ H → T (G □ H) == T G ◯ T H}
      (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
      (λ {(g , gpt) → Trunc-elim
        {B = λ H → T ([ g , gpt ] □ H) == T [ g , gpt ] ◯ T H}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ {(h , hpt) → ap [_] (comp-lemma g h gpt hpt)})}) 
      G H}
    where
    _◯_ = GroupStructure.comp (Group.group-struct (C n X))
    _□_ = GroupStructure.comp (Group.group-struct (C n Y))
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


{- Eilenberg-Steenrod Axioms 
 - Currently including:
   ∙ Suspension 
   ∙ Non-truncated and Truncated versions of Exactness
   ∙ Finite Additivity 
 -}

{- Suspension Axiom -}

abstract
  C-Susp : ∀ {j} (n : ℕ) (X : Ptd j) → C (S n) (Ptd-Susp X) == C n X
  C-Susp n X = SuspAdjointLoopIso.iso X (Ptd-KG (S (S n))) 
               ∙ ap (→Ω-Group X) spec
    where
    spec : Ptd-Ω (Ptd-KG (S (S n))) == Ptd-KG (S n)
    spec = spectrum (S n)

{- Non-truncated Exactness Axiom -}

{- pointed version of the function [cfcod] from lib.types.Cofiber -}
ptd-cfcod : ∀ {j k} {X : Ptd j} {Y : Ptd k} (F : fst (X ∙→ Y))
  → fst (Y ∙→ Ptd-Cof (fst F))
ptd-cfcod {X = X} (f , fpt) = 
  (cfcod f , ap (cfcod f) (! fpt) ∙ ! (cfglue f (snd X)))

module _ {j k} (n : ℕ) {X : Ptd j} {Y : Ptd k} where

  {- in image of (uCF n (ptd-cfcod F)) ⇒ in kernel of (uCF n F) -}
  abstract
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
  abstract
    uC-Exact-ktoi : (F : fst (X ∙→ Y)) 
      → is-exact-ktoi (uCF n (ptd-cfcod F)) (uCF n F)
    uC-Exact-ktoi (f , fpt) (h , hpt) p = 
      (g , ! q ∙ hpt) , 
      pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (λ w → w ∙ hpt) (!-inv-r q))
      where 
      g : Cofiber f → Ω (Ptd-KG (S n))
      g = CofiberRec.f f idp h (! ∘ app= (ap fst p))

      q : h (snd Y) == g (cfbase f)
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
  abstract
    C-Exact-itok : (F : fst (X ∙→ Y)) 
      → is-exact-itok (CF n (ptd-cfcod F)) (CF n F)
    C-Exact-itok F = 
      Trunc-elim 
        {B = λ tG → fst (CF n F) (fst (CF n (ptd-cfcod F)) tG) == Cid n X}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ G → ap [_] (uC-Exact-itok n F G))

  abstract
    C-Exact-itok-mere : (F : fst (X ∙→ Y))
      → is-exact-itok-mere (CF n (ptd-cfcod F)) (CF n F)
    C-Exact-itok-mere F = 
      itok-to-mere (CF n (ptd-cfcod F)) (CF n F) Trunc-level (C-Exact-itok F)

  {- in kernel of (CF n F) ⇒ merely in image of (CF n (ptd-cfcod F)) -}
  abstract
    C-Exact-ktoi-mere : (F : fst (X ∙→ Y))
      → is-exact-ktoi-mere (CF n (ptd-cfcod F)) (CF n F)
    C-Exact-ktoi-mere F = 
      Trunc-elim
        {B = λ tH → fst (CF n F) tH == Cid n X
           → Trunc ⟨-1⟩ (Σ (CEl n (Ptd-Cof (fst F))) 
                           (λ tK → fst (CF n (ptd-cfcod F)) tK == tH))}
        (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
        (λ H tp → Trunc-rec Trunc-level (lemma H) (–> (Trunc=-equiv _ _) tp))
        where 
        lemma : (H : uCEl n Y) 
          → fst (uCF n F) H == uCid n X
          → Trunc ⟨-1⟩ (Σ (CEl n (Ptd-Cof (fst F))) 
                          (λ tK → fst (CF n (ptd-cfcod F)) tK == [ H ]))
        lemma H p = [ [ fst (uC-Exact-ktoi n F H p) ] , 
                        ap [_] (snd (uC-Exact-ktoi n F H p)) ]

{- Finite Additivity Axiom -}
module _ {j k} (n : ℕ) (X : Ptd j) (Y : Ptd k) where

  private
    _◯_ = GroupStructure.comp (Group.group-struct (C n (Ptd-Wedge X Y)))
    _□_ = GroupStructure.comp (Group.group-struct ((C n X) ×G (C n Y)))

    R : CEl n (Ptd-Wedge X Y) → (CEl n X) × (CEl n Y)
    R = Trunc-rec (×-level Trunc-level Trunc-level) 
      (λ {H → ([ H ∘ptd ptd-winl ] , [ H ∘ptd ptd-winr ])})

    L : (CEl n X) × (CEl n Y) → CEl n (Ptd-Wedge X Y)
    L (tF , tG) = Trunc-rec 
      Trunc-level 
      (λ {(f , fpt) → Trunc-rec 
        Trunc-level 
        (λ {(g , gpt) → [ WedgeRec.f f g (fpt ∙ ! gpt) , fpt ]})
        tG})
      tF

    abstract
      R-L : ∀ y → R (L y) == y
      R-L (tF , tG) = Trunc-elim
        {B = λ tF → ∀ tG → R (L (tF , tG)) == (tF , tG)}
        (λ _ → Π-level (λ _ → 
                 =-preserves-level _ (×-level Trunc-level Trunc-level)))
        (λ {(f , fpt) → Trunc-elim
          {B = λ tG → R (L ([ f , fpt ] , tG)) == ([ f , fpt ] , tG)}
          (λ _ → =-preserves-level _ (×-level Trunc-level Trunc-level))
          (λ {(g , gpt) → 
             pair×= idp 
               (ap [_] (pair= idp 
                          (lemma (WedgeRec.f f g (fpt ∙ ! gpt)) 
                                 wglue fpt gpt 
                                 (WedgeRec.glue-β f g (fpt ∙ ! gpt) tt))))})})
        tF tG
        where
        lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
          {a₁ a₂ : A} (p : a₁ == a₂) {b : B} (q : f a₁ == b) (r : f a₂ == b)
          → ap f p == q ∙ ! r → ap f (! p) ∙ q == r
        lemma f idp idp r p = ap ! p ∙ !-! r

    abstract
      L-R : ∀ x → L (R x) == x
      L-R = Trunc-elim
        {B = λ tH → L (R tH) == tH}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ H → ap [_] (pair= 
          (λ= (L-R-fst H))
          (↓-app=cst-in (ap (λ w → w ∙ snd H)
                            (! (app=-β (L-R-fst H) (snd (Ptd-Wedge X Y))))))))
        where
        {- the first component of detruncated L (R [ h , hpt ]);
         - given a name for sake of space -}
        wh : fst (Ptd-Wedge X Y ∙→ Ptd-Ω (Ptd-KG (S n)))
          → (Wedge X Y → Ω (Ptd-KG (S n)))
        wh (h , hpt) = 
          WedgeRec.f (h ∘ winl) (h ∘ winr) 
            (snd ((h , hpt) ∘ptd ptd-winl) ∙ ! (snd ((h , hpt) ∘ptd ptd-winr)))

        lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
          {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
          → ap f p == q ∙ ! (ap f (! p) ∙ q)
        lemma f idp idp = idp

        L-R-fst : (H : fst (Ptd-Wedge X Y ∙→ Ptd-Ω (Ptd-KG (S n))))
          → ∀ w → (wh H) w == fst H w
        L-R-fst (h , hpt) = Wedge-elim
          {P = λ w → wh (h , hpt) w == h w}
          (λ _ → idp)
          (λ _ → idp)
          (↓-='-in 
            (ap h wglue
               =⟨ lemma h (glue unit) hpt ⟩
             snd ((h , hpt) ∘ptd ptd-winl) ∙ ! (snd ((h , hpt) ∘ptd ptd-winr))
               =⟨ ! (WedgeRec.glue-β (h ∘ winl) (h ∘ winr) _ tt) ⟩
             ap (wh (h , hpt)) wglue ∎ ))

    abstract
      pres-ident : R (Cid n (Ptd-Wedge X Y)) == (Cid n X , Cid n Y)
      pres-ident = 
        pair×= idp (ap [_] (pair= idp (∙-unit-r _ ∙ ap-cst idp (! wglue))))

    abstract
      pres-comp : (tF tG : CEl n (Ptd-Wedge X Y)) 
        → R (tF ◯ tG) == (R tF) □ (R tG)
      pres-comp = 
        Trunc-elim
          {B = λ tF → (tG : CEl n (Ptd-Wedge X Y)) 
                    → R (tF ◯ tG) == (R tF) □ (R tG)}
          (λ _ → Π-level (λ _ → 
                   =-preserves-level _ (×-level Trunc-level Trunc-level)))
          (λ F → Trunc-elim
            {B = λ tG → R ([ F ] ◯ tG) == (R [ F ]) □ (R tG)}
            (λ _ → =-preserves-level _ (×-level Trunc-level Trunc-level))
            (λ G → pair×= idp (ap [_] (pair= 
              idp 
              (lemma (fst F) (fst G) (! (glue unit)) (snd F) (snd G))))))
        where 
        lemma : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} {b₀ : B}
          {p q : b₀ == b₀} (f : A → b₀ == b₀) (g : A → b₀ == b₀) 
          (r : a₁ == a₂) (α : f a₂ == p) (β : g a₂ == q)
          → ap (λ x → f x ∙ g x) r ∙ ap2 _∙_ α β
            == ap2 _∙_ (ap f r ∙ α) (ap g r ∙ β)
        lemma f g idp idp idp = idp

  abstract
    C-Additivity : C n (Ptd-Wedge X Y) == (C n X) ×G (C n Y)
    C-Additivity = group-iso (group-hom R pres-ident pres-comp) (is-eq R L R-L L-R)
