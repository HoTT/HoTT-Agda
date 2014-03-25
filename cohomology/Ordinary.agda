{-# OPTIONS --without-K #-}

open import HoTT 
open import homotopy.KGn
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Exactness
open import cohomology.Choice
open import cohomology.OrdinaryTheory

module cohomology.Ordinary {i} (G : Group i) (G-abelian : is-abelian G) where

open KGnExplicit G G-abelian using (Ptd-KG; KG-conn; spectrum)

{- Definition of cohomology group C -}
module _ (n : ℕ) (X : Ptd i) where
  {- Ordinary cohomology group -}
  C : Group i
  C = →Ω-Group X (Ptd-KG (S n))

  {- Underlying space of cohomology group -}
  CEl : Type i
  CEl = Group.El C -- Ptd-Trunc ⟨0⟩ (fst (X ∙→ Ptd-Ω (Ptd-KG (S n))))

  {- Basepoint of underlying space -}
  Cid : CEl
  Cid = GroupStructure.ident (Group.group-struct C)

  {- Underlying pointed space of cohomology group -}
  Ptd-CEl : Ptd i
  Ptd-CEl = ∙[ Group.El C , Cid ]

  {- Untruncated versions of the cohomology spaces -}
  uCEl : Type i -- CEl ≡ Trunc ⟨0⟩ uCEl
  uCEl = fst (X ∙→ Ptd-Ω (Ptd-KG (S n)))

  Ptd-uCEl : Ptd i
  Ptd-uCEl = X ∙→ Ptd-Ω (Ptd-KG (S n))

  uCid : uCEl
  uCid = snd Ptd-uCEl

{- CF, the functorial action of C:
 - contravariant functor from pointed spaces to abelian groups -}
module _ (n : ℕ) {X Y : Ptd i} where

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


{- Eilenberg-Steenrod Axioms -}

{- Suspension Axiom -}

abstract
  C-Susp : (n : ℕ) (X : Ptd i) → C (S n) (Ptd-Susp X) == C n X
  C-Susp n X = SuspAdjointLoopIso.iso X (Ptd-KG (S (S n))) 
               ∙ ap (→Ω-Group X) spec
    where
    spec : Ptd-Ω (Ptd-KG (S (S n))) == Ptd-KG (S n)
    spec = spectrum (S n)

{- Non-truncated Exactness Axiom -}

module _ (n : ℕ) {X Y : Ptd i} where

  {- in image of (uCF n (ptd-cfcod F)) ⇒ in kernel of (uCF n F) -}
  abstract
    uC-exact-itok : (F : fst (X ∙→ Y)) 
      → is-exact-itok (uCF n (ptd-cfcod F)) (uCF n F)
    uC-exact-itok (f , fpt) (g , gpt) = pair= 
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
    uC-exact-ktoi : (F : fst (X ∙→ Y)) 
      → is-exact-ktoi (uCF n (ptd-cfcod F)) (uCF n F)
    uC-exact-ktoi (f , fpt) (h , hpt) p = 
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

module _ (n : ℕ) {X Y : Ptd i} where

  {- in image of (CF n (ptd-cfcod F)) ⇒ in kernel of (CF n F) -}
  abstract
    C-exact-itok : (F : fst (X ∙→ Y)) 
      → is-exact-itok (CF n (ptd-cfcod F)) (CF n F)
    C-exact-itok F = 
      Trunc-elim 
        {B = λ tG → fst (CF n F) (fst (CF n (ptd-cfcod F)) tG) == Cid n X}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ G → ap [_] (uC-exact-itok n F G))

  abstract
    C-exact-itok-mere : (F : fst (X ∙→ Y))
      → is-exact-itok-mere (CF n (ptd-cfcod F)) (CF n F)
    C-exact-itok-mere F = 
      itok-to-mere (CF n (ptd-cfcod F)) (CF n F) Trunc-level (C-exact-itok F)

  {- in kernel of (CF n F) ⇒ merely in image of (CF n (ptd-cfcod F)) -}
  abstract
    C-exact-ktoi-mere : (F : fst (X ∙→ Y))
      → is-exact-ktoi-mere (CF n (ptd-cfcod F)) (CF n F)
    C-exact-ktoi-mere F = 
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
        lemma H p = [ [ fst (uC-exact-ktoi n F H p) ] , 
                        ap [_] (snd (uC-exact-ktoi n F H p)) ]

{- General Additivity Axiom -}
module _ (n : ℕ) {A : Type i} (X : A → Ptd i) 
  (ac : (W : A → Type i) → (∀ a → has-level ⟨ n ⟩ (W a)) → has-choice ⟨0⟩ A W)
  where

  uie : has-choice ⟨0⟩ A (uCEl n ∘ X)
  uie = ac (uCEl n ∘ X) (λ _ → ∙→-level (Trunc-level {n = S ⟨ n ⟩} _ _))

  module _ where
    R' : CEl n (Ptd-BigWedge X) → Trunc ⟨0⟩ (Π A (uCEl n ∘ X))
    R' = Trunc-rec Trunc-level (λ H → [ (λ a → H ∘ptd ptd-bwin a) ])

    R : CEl n (Ptd-BigWedge X) → Π A (CEl n ∘ X)
    R = unchoose ∘ R'

    L' : Trunc ⟨0⟩ (Π A (uCEl n ∘ X)) → CEl n (Ptd-BigWedge X)
    L' = Trunc-rec Trunc-level 
      (λ K → [ BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K) , 
               idp ])

    L : Π A (CEl n ∘ X) → CEl n (Ptd-BigWedge X)
    L = L' ∘ (is-equiv.g uie)

    R'-L' : ∀ y → R' (L' y) == y
    R'-L' = Trunc-elim
      {B = λ tK → R' (L' tK) == tK}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ K → ap [_] (λ= (λ a → pair= idp $
        ap (BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K)) (! (bwglue a)) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap (BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K)) (! (bwglue a)) 
          =⟨ ap-! (BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K)) (bwglue a) ⟩
        ! (ap (BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K)) (bwglue a)) 
          =⟨ ap ! (BigWedgeRec.glue-β idp (fst ∘ K) (! ∘ snd ∘ K) a) ⟩
        ! (! (snd (K a)))
          =⟨ !-! (snd (K a)) ⟩
        snd (K a) ∎)))

    L'-R' : ∀ x → L' (R' x) == x
    L'-R' = Trunc-elim
      {B = λ tH → L' (R' tH) == tH}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ {(h , hpt) → ap [_] (pair= 
         (λ= (L-R-fst (h , hpt)))
         (↓-app=cst-in $ ! $
            ap (λ w → w ∙ hpt) (app=-β (L-R-fst (h , hpt)) bwbase)
            ∙ !-inv-l hpt))})
      where
      wh : fst (Ptd-BigWedge X ∙→ Ptd-Ω (Ptd-KG (S n)))
        → (BigWedge X → Ω (Ptd-KG (S n)))
      wh (h , hpt) = 
        BigWedgeRec.f idp (λ a → h ∘ bwin a)
          (λ a → ! (ap h (! (bwglue a)) ∙ hpt))

      lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
        → ! q ∙ ap f p == ! (ap f (! p) ∙ q)
      lemma f idp idp = idp

      L-R-fst : (H : fst (Ptd-BigWedge X ∙→ Ptd-Ω (Ptd-KG (S n))))
        → ∀ w → (wh H) w == fst H w
      L-R-fst (h , hpt) = BigWedge-elim 
        {P = λ w → wh (h , hpt) w == h w}
        (! hpt)
        (λ _ _ → idp)
        (λ a → ↓-='-in $
           ! hpt ∙ ap h (bwglue a)
             =⟨ lemma h (bwglue a) hpt ⟩
           ! (ap h (! (bwglue a)) ∙ hpt)
             =⟨ ! (BigWedgeRec.glue-β idp (λ a → h ∘ bwin a) 
                     (λ a → ! (ap h (! (bwglue a)) ∙ hpt)) a) ⟩
           ap (wh (h , hpt)) (bwglue a) ∎)

    abstract
      R'-is-equiv : is-equiv R'
      R'-is-equiv = is-eq R' L' R'-L' L'-R'
      
    abstract
      pres-ident : R (Cid n (Ptd-BigWedge X)) == (Cid n ∘ X)
      pres-ident = 
        λ= (λ a → ap [_] (pair= idp (∙-unit-r _ ∙ ap-cst idp (! (bwglue a)))))

    _◯_ = GroupStructure.comp (Group.group-struct (C n (Ptd-BigWedge X)))
    _□_ = GroupStructure.comp (Group.group-struct (ΠG A (C n ∘ X)))

    abstract
      pres-comp : (tF tG : CEl n (Ptd-BigWedge X)) 
        → R (tF ◯ tG) == (R tF) □ (R tG)
      pres-comp = Trunc-elim 
        {B = λ tF → ∀ tG → R (tF ◯ tG) == (R tF) □ (R tG)}
        (λ _ → Π-level (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level))))
        (λ F → Trunc-elim
          {B = λ tG → R ([ F ] ◯ tG) == R [ F ] □ R tG}
          (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
          (λ G → λ= (λ a → ap [_] (pair= 
            idp 
            (lemma (fst F) (fst G) (! (bwglue a)) (snd F) (snd G))))))
        where
        lemma : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} {b₀ : B}
          {p q : b₀ == b₀} (f : A → b₀ == b₀) (g : A → b₀ == b₀) 
          (r : a₁ == a₂) (α : f a₂ == p) (β : g a₂ == q)
          → ap (λ x → f x ∙ g x) r ∙ ap2 _∙_ α β
            == ap2 _∙_ (ap f r ∙ α) (ap g r ∙ β)
        lemma f g idp idp idp = idp

    abstract
      R-hom : GroupHom (C n (Ptd-BigWedge X)) (ΠG A (C n ∘ X))
      R-hom = group-hom R pres-ident pres-comp

      R-is-equiv : is-equiv (GroupHom.f R-hom)
      R-is-equiv = uie ∘ise R'-is-equiv

  abstract
    C-additive : C n (Ptd-BigWedge X) == ΠG A (C n ∘ X)
    C-additive = group-iso R-hom R-is-equiv

{- Dimension Axiom -}
abstract
  C-dimensionS : (n : ℕ) → C (S n) (Ptd-Lift Ptd-Bool) == LiftUnit-group
  C-dimensionS n = contr-iso-LiftUnit _ $ connected-at-level-is-contr 
    (Trunc-level {n = ⟨0⟩})
    (Trunc-preserves-conn ⟨0⟩ 
      (transport (λ B → is-connected ⟨0⟩ B) 
        (! (Bool∙→-path _))
        (path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                 (KG-conn (S n))))))

C-Cohomology : OrdinaryTheory i
C-Cohomology = record {
  C = C;
  F-hom = CF-hom;
  C-Susp = C-Susp;
  C-exact-itok-mere = C-exact-itok-mere;
  C-exact-ktoi-mere = C-exact-ktoi-mere;
  C-additive = C-additive;
  C-dimensionS = C-dimensionS}
