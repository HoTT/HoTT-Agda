{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.KGn
open import homotopy.SuspAdjointLoop
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Exactness
open import cohomology.Choice

module cohomology.OrdinaryNatModel
  {i} (G : Group i) (G-abelian : is-abelian G) where

open KGnExplicit G G-abelian using (⊙KG; KG-level; KG-conn; spectrum)

private
  ⊙ℤKG : (n : ℤ) → Ptd i
  ⊙ℤKG O = ⊙Ω (⊙KG 1)
  ⊙ℤKG (pos m) = ⊙Ω (⊙KG (S (S m)))
  ⊙ℤKG (neg m) = ⊙Ω (⊙Lift ⊙Unit)

{- Definition of cohomology group C -}
module _ (n : ℕ) (X : Ptd i) where
  {- Ordinary cohomology group -}
  C : Group i
  C = →Ω-Group X (⊙KG (S n))

  {- some convenient abbreviations -}
  CEl = Group.El C
  Cid = Group.ident C
  ⊙CEl = Group.⊙El C

  {- Untruncated versions of the cohomology spaces -}
  ⊙uCEl : Ptd i
  ⊙uCEl = X ⊙→ ⊙Ω (⊙KG (S n))

  uCEl = fst ⊙uCEl
  uCid = snd ⊙uCEl

{- C n X is an abelian group -}
C-abelian : (n : ℕ) (X : Ptd i) → is-abelian (C n X)
C-abelian n X =
  transport (is-abelian ∘ →Ω-Group X) (spectrum (S n)) (C-abelian-lemma n X)
  where
  C-abelian-lemma : (n : ℕ) (X : Ptd i)
    → is-abelian (→Ω-Group X (⊙Ω (⊙KG (S (S n)))))
  C-abelian-lemma n X = Trunc-elim
    (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
    (λ {(f , fpt) → Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ {(g , gpt) → ap [_] $ ⊙λ=
        (λ x → conc^2-comm (f x) (g x))
        (lemma fpt gpt)})})
    where
    lemma : ∀ {i} {X : Ptd i} {α β : Ω^ 2 X}
      (γ : α == idp^ 2) (δ : β == idp^ 2)
      → ap2 _∙_ γ δ == conc^2-comm α β ∙ ap2 _∙_ δ γ
    lemma idp idp = idp

{- CF, the functorial action of C:
 - contravariant functor from pointed spaces to abelian groups -}
module _ (n : ℕ) {X Y : Ptd i} where

  {- untruncated version - from pointed spaces to pointed spaces -}
  uCF : fst (X ⊙→ Y) → fst (⊙uCEl n Y ⊙→ ⊙uCEl n X)
  uCF F =
    (λ G → G ⊙∘ F) ,
    pair= idp (∙-unit-r _ ∙ ap-cst idp (snd F))

  CF-hom : fst (X ⊙→ Y) → GroupHom (C n Y) (C n X)
  CF-hom (f , fpt) = record {
    f = T;
    pres-comp = λ G H → Trunc-elim
      {P = λ G → ∀ H → T (G □ H) == T G ◯ T H}
      (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
      (λ {(g , gpt) → Trunc-elim
        {P = λ H → T ([ g , gpt ] □ H) == T [ g , gpt ] ◯ T H}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ {(h , hpt) → ap [_] (comp-lemma g h gpt hpt)})})
      G H}
    where
    _◯_ = Group.comp (C n X)
    _□_ = Group.comp (C n Y)
    T = Trunc-fmap (fst (uCF (f , fpt)))

    lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
      {a : A} {b : B} {c₁ c₂ : C}
      (f : A → B) (g h : B → C) (_⊙_ : C → C → C)
      (fpt : f a == b) (gpt : g b == c₁) (hpt : h b == c₂)
      → ap (λ x → g x ⊙ h x) fpt ∙ ap2 _⊙_ gpt hpt
        == ap2 _⊙_ (ap g fpt ∙ gpt) (ap h fpt ∙ hpt)
    lemma f g h _⊙_ idp idp idp = idp

    comp-lemma : (g h : fst Y → Ω (⊙KG (S n)))
      (gpt : g (snd Y) == idp) (hpt : h (snd Y) == idp) →
      Path {A = fst (X ⊙→ ⊙Ω (⊙KG (S n)))}
        ((λ x → g (f x) ∙ h (f x)) , ap (λ x → g x ∙ h x) fpt ∙ ap2 _∙_ gpt hpt)
        ((λ x → g (f x) ∙ h (f x)) , ap2 _∙_ (ap g fpt ∙ gpt) (ap h fpt ∙ hpt))
    comp-lemma g h gpt hpt = pair= idp (lemma f g h _∙_ fpt gpt hpt)

  CF : fst (X ⊙→ Y) → fst (⊙CEl n Y ⊙→ ⊙CEl n X)
  CF F = GroupHom.⊙f (CF-hom F)

{- CF-hom is a functor from pointed spaces to abelian groups -}
module _ (n : ℕ) {X : Ptd i} where

  CF-ident : CF-hom n {X} {X} (⊙idf X) == idhom (C n X)
  CF-ident = hom= _ _ $ λ= $ Trunc-elim
    {P = λ tx → Trunc-fmap (λ x → x) tx == tx}
    (λ _ → =-preserves-level _ Trunc-level)
    (λ _ → idp)

  CF-comp : {Y Z : Ptd i} (G : fst (Y ⊙→ Z)) (F : fst (X ⊙→ Y))
    → CF-hom n (G ⊙∘ F) == CF-hom n F ∘hom CF-hom n G
  CF-comp G F = hom= _ _ $ λ= $ Trunc-elim
    {P = λ tH → Trunc-fmap (λ H → H ⊙∘ (G ⊙∘ F)) tH
                == Trunc-fmap (λ K → K ⊙∘ F) (Trunc-fmap (λ H → H ⊙∘ G) tH)}
    (λ _ → =-preserves-level _ Trunc-level)
    (λ H → ap [_] (! (⊙∘-assoc H G F)))

{- Eilenberg-Steenrod Axioms -}

{- Suspension Axioms -}

abstract
  C-SuspS : (n : ℕ) (X : Ptd i) → C (S n) (⊙Susp X) == C n X
  C-SuspS n X = SuspAdjointLoopIso.iso X (⊙KG (S (S n)))
               ∙ ap (→Ω-Group X) spec
    where
    spec : ⊙Ω (⊙KG (S (S n))) == ⊙KG (S n)
    spec = spectrum (S n)

abstract
  C-SuspO : (X : Ptd i) → C 0 (⊙Susp X) == 0G
  C-SuspO X = contr-iso-LiftUnit _ $ inhab-prop-is-contr
    (Cid 0 (⊙Susp X))
    (Trunc-preserves-level ⟨0⟩ $
      equiv-preserves-level ((SuspAdjointLoop.eqv X (⊙Ω (⊙KG 1)))⁻¹)
        (⊙→-level (KG-level 1 _ _ _ _)))

{- Non-truncated Exactness Axiom -}

module _ (n : ℕ) {X Y : Ptd i} where

  {- uCF n (⊙cfcod F) ∘ uCF n F is constant -}
  abstract
    uC-exact-itok-lemma : (F : fst (X ⊙→ Y)) (G : uCEl n (⊙Cof F))
      → fst (uCF n F) (fst (uCF n (⊙cfcod F)) G) == uCid n X
    uC-exact-itok-lemma (f , fpt) (g , gpt) = pair=
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

  {- in kernel of (uCF n F) ⇒ in image of (uCF n (⊙cfcod F)) -}
  abstract
    uC-exact-ktoi-lemma : (F : fst (X ⊙→ Y)) (G : uCEl n Y)
      → fst (uCF n F) G == uCid n X
      → Σ (uCEl n (⊙Cof F)) (λ H → fst (uCF n (⊙cfcod F)) H == G)
    uC-exact-ktoi-lemma (f , fpt) (h , hpt) p =
      (g , ! q ∙ hpt) ,
      pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (λ w → w ∙ hpt) (!-inv-r q))
      where
      g : Cofiber f → Ω (⊙KG (S n))
      g = CofiberRec.f f idp h (! ∘ app= (ap fst p))

      q : h (snd Y) == g (cfbase f)
      q = ap g (snd (⊙cfcod (f , fpt)))

      {- path induction in place of simple but tedious algebraic manipulation -}
      lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
        {a₁ a₂ : A} {b : B} (f : A → B) (g : B → C)
        (p : a₁ == a₂) (q : b == f a₂)
        → ap g (ap f p ∙ ! q) == ap (g ∘ f) p ∙ ! (ap g q)
      lemma f g idp q = ap-! g q

{- Truncated Exactness Axiom -}

module _ (n : ℕ) {X Y : Ptd i} where

  {- in image of (CF n (⊙cfcod F)) ⇒ in kernel of (CF n F) -}
  abstract
    C-exact-itok : (F : fst (X ⊙→ Y))
      → is-exact-itok (CF n (⊙cfcod F)) (CF n F)
    C-exact-itok F =
      itok-alt-in (CF n (⊙cfcod F)) (CF n F) (Trunc-level {n = ⟨0⟩}) $
        Trunc-elim (λ _ → =-preserves-level _ (Trunc-level {n = ⟨0⟩}))
          (ap [_] ∘ uC-exact-itok-lemma n F)

  {- in kernel of (CF n F) ⇒ in image of (CF n (⊙cfcod F)) -}
  abstract
    C-exact-ktoi : (F : fst (X ⊙→ Y))
      → is-exact-ktoi (CF n (⊙cfcod F)) (CF n F)
    C-exact-ktoi F =
      Trunc-elim
        {P = λ tH → fst (CF n F) tH == Cid n X
           → Trunc ⟨-1⟩ (Σ (CEl n (⊙Cof F))
                           (λ tK → fst (CF n (⊙cfcod F)) tK == tH))}
        (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
        (λ H tp → Trunc-rec Trunc-level (lemma H) (–> (Trunc=-equiv _ _) tp))
        where
        lemma : (H : uCEl n Y)
          → fst (uCF n F) H == uCid n X
          → Trunc ⟨-1⟩ (Σ (CEl n (⊙Cof F))
                          (λ tK → fst (CF n (⊙cfcod F)) tK == [ H ]))
        lemma H p = [ [ fst (uC-exact-ktoi-lemma n F H p) ] ,
                        ap [_] (snd (uC-exact-ktoi-lemma n F H p)) ]

  C-exact : (F : fst (X ⊙→ Y)) → is-exact (CF n (⊙cfcod F)) (CF n F)
  C-exact F = record {itok = C-exact-itok F; ktoi = C-exact-ktoi F}

{- General Additivity Axiom -}
module _ (n : ℕ) {A : Type i} (X : A → Ptd i)
  (ac : (W : A → Type i) → (∀ a → has-level ⟨ n ⟩ (W a)) → has-choice ⟨0⟩ A W)
  where

  uie : has-choice ⟨0⟩ A (uCEl n ∘ X)
  uie = ac (uCEl n ∘ X) (λ _ → ⊙→-level (Trunc-level {n = S ⟨ n ⟩} _ _))

  module _ where
    R' : CEl n (⊙BigWedge X) → Trunc ⟨0⟩ (Π A (uCEl n ∘ X))
    R' = Trunc-rec Trunc-level (λ H → [ (λ a → H ⊙∘ ⊙bwin a) ])

    R : CEl n (⊙BigWedge X) → Π A (CEl n ∘ X)
    R = unchoose ∘ R'

    L' : Trunc ⟨0⟩ (Π A (uCEl n ∘ X)) → CEl n (⊙BigWedge X)
    L' = Trunc-rec Trunc-level
      (λ K → [ BigWedgeRec.f idp (fst ∘ K) (! ∘ snd ∘ K) ,
               idp ])

    L : Π A (CEl n ∘ X) → CEl n (⊙BigWedge X)
    L = L' ∘ (is-equiv.g uie)

    R'-L' : ∀ y → R' (L' y) == y
    R'-L' = Trunc-elim
      {P = λ tK → R' (L' tK) == tK}
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
      {P = λ tH → L' (R' tH) == tH}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ {(h , hpt) → ap [_] (pair=
         (λ= (L-R-fst (h , hpt)))
         (↓-app=cst-in $ ! $
            ap (λ w → w ∙ hpt) (app=-β (L-R-fst (h , hpt)) bwbase)
            ∙ !-inv-l hpt))})
      where
      wh : fst (⊙BigWedge X ⊙→ ⊙Ω (⊙KG (S n)))
        → (BigWedge X → Ω (⊙KG (S n)))
      wh (h , hpt) =
        BigWedgeRec.f idp (λ a → h ∘ bwin a)
          (λ a → ! (ap h (! (bwglue a)) ∙ hpt))

      lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
        → ! q ∙ ap f p == ! (ap f (! p) ∙ q)
      lemma f idp idp = idp

      L-R-fst : (H : fst (⊙BigWedge X ⊙→ ⊙Ω (⊙KG (S n))))
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

    _◯_ = Group.comp (C n (⊙BigWedge X))
    _□_ = Group.comp (ΠG A (C n ∘ X))

    abstract
      pres-comp : (tF tG : CEl n (⊙BigWedge X))
        → R (tF ◯ tG) == (R tF) □ (R tG)
      pres-comp = Trunc-elim
        {P = λ tF → ∀ tG → R (tF ◯ tG) == (R tF) □ (R tG)}
        (λ _ → Π-level (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level))))
        (λ F → Trunc-elim
          {P = λ tG → R ([ F ] ◯ tG) == R [ F ] □ R tG}
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
      R-hom : GroupHom (C n (⊙BigWedge X)) (ΠG A (C n ∘ X))
      R-hom = group-hom R pres-comp

      R-is-equiv : is-equiv (GroupHom.f R-hom)
      R-is-equiv = uie ∘ise R'-is-equiv

  abstract
    C-additive : C n (⊙BigWedge X) == ΠG A (C n ∘ X)
    C-additive = group-iso R-hom R-is-equiv

{- Dimension Axiom -}
abstract
  C-dimension-S : (n : ℕ) → C (S n) (⊙Sphere 0) == 0G
  C-dimension-S n = contr-iso-LiftUnit _ $ connected-at-level-is-contr
    (Trunc-level {n = ⟨0⟩})
    (Trunc-preserves-conn ⟨0⟩
      (transport (λ B → is-connected ⟨0⟩ B)
        (! (Bool⊙→-path _))
        (path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                 (KG-conn (S n))))))

