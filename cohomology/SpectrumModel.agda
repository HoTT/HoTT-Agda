{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Theory
open import cohomology.Exactness
open import cohomology.Choice

module cohomology.SpectrumModel
  {i} (E : ℤ → Ptd i) (spectrum : (n : ℤ) → ⊙Ω (E (succ n)) == E n) where

module SpectrumModel where

  {- Definition of cohomology group C -}
  module _ (n : ℤ) (X : Ptd i) where
    C : Group i
    C = →Ω-Group X (E (succ n))

    {- convenient abbreviations -}
    CEl = Group.El C
    ⊙CEl = Group.⊙El C
    Cid = Group.ident C

    {- before truncation -}
    ⊙uCEl : Ptd i
    ⊙uCEl = X ⊙→ ⊙Ω (E (succ n))

    uCEl = fst ⊙uCEl
    uCid = snd ⊙uCEl

  {- Cⁿ(X) is an abelian group -}
  C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)
  C-abelian n X =
    transport (is-abelian ∘ →Ω-Group X) (spectrum (succ n)) C-abelian-lemma
    where
    pt-lemma : ∀ {i} {X : Ptd i} {α β : Ω^ 2 X}
      (γ : α == idp^ 2) (δ : β == idp^ 2)
      → ap2 _∙_ γ δ == conc^2-comm α β ∙ ap2 _∙_ δ γ
    pt-lemma idp idp = idp

    C-abelian-lemma = Trunc-elim
      (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
      (λ {(f , fpt) → Trunc-elim
        (λ _ → =-preserves-level _ Trunc-level)
        (λ {(g , gpt) → ap [_] $ ⊙λ=
          (λ x → conc^2-comm (f x) (g x))
          (pt-lemma fpt gpt)})})

  {- CF, the functorial action of C:
   - contravariant functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- before truncation - from pointed spaces to pointed spaces -}
    uCF : fst (X ⊙→ Y) → fst (⊙uCEl n Y ⊙→ ⊙uCEl n X)
    uCF f =
      ((λ g → g ⊙∘ f) ,
       pair= idp (∙-unit-r _ ∙ ap-cst idp (snd f)))

    CF-hom : fst (X ⊙→ Y) → GroupHom (C n Y) (C n X)
    CF-hom f = record {
      f = Trunc-fmap {n = ⟨0⟩} (fst (uCF f));
      pres-comp = Trunc-elim
        (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
        (λ g → Trunc-elim
          (λ _ → =-preserves-level _ Trunc-level)
          (λ h → ap [_] $ pair= idp (comp-snd _∙_ f g h)))}
      where
      comp-snd : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {C : Type k}
        {c₁ c₂ : C} (_⊕_ : C → C → C) (f : fst (X ⊙→ Y))
        (g : fst (Y ⊙→ ⊙[ C , c₁ ])) (h : fst (Y ⊙→ ⊙[ C , c₂ ]))
        → ap (λ x → fst g x ⊕ fst h x) (snd f) ∙ ap2 _⊕_ (snd g) (snd h)
          == ap2 _⊕_ (ap (fst g) (snd f) ∙ snd g) (ap (fst h) (snd f) ∙ snd h)
      comp-snd _⊕_ (_ , idp) (_ , idp) (_ , idp) = idp

    CF : fst (X ⊙→ Y) → fst (⊙CEl n Y ⊙→ ⊙CEl n X)
    CF F = GroupHom.⊙f (CF-hom F)

  {- CF-hom is a functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X : Ptd i} where

    CF-ident : CF-hom n {X} {X} (⊙idf X) == idhom (C n X)
    CF-ident = hom= _ _ $ λ= $ Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ _ → idp)

    CF-comp : {Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → CF-hom n (g ⊙∘ f) == CF-hom n f ∘hom CF-hom n g
    CF-comp g f = hom= _ _ $ λ= $ Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ h → ap [_] (! (⊙∘-assoc h g f)))

  {- Eilenberg-Steenrod Axioms -}

  {- Suspension Axiom -}
  C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) == C n X
  C-Susp n X =
    SuspAdjointLoopIso.iso X (E (succ (succ n)))
    ∙ ap (→Ω-Group X) (spectrum (succ n))


  {- Non-truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- [uCF n (⊙cfcod f) ∘ uCF n f] is constant -}
    uC-exact-itok-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n (⊙Cof f))
      → fst (uCF n f) (fst (uCF n (⊙cfcod f)) g) == uCid n X
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
        lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
          {a₁ a₂ : A} {b : B} {c : C} (f : A → B) (g : B → C)
          (p : a₁ == a₂) (q : f a₁ == b) (r : g b == c)
          → ap (g ∘ f) p ∙ ap g (ap f (! p) ∙ q) ∙ r == ap g q ∙ r
        lemma f g idp idp idp = idp

    {- in kernel of [uCF n f] ⇒ in image of [uCF n (⊙cfcod f)] -}
    uC-exact-ktoi-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n Y)
      → fst (uCF n f) g == uCid n X
      → Σ (uCEl n (⊙Cof f)) (λ h → fst (uCF n (⊙cfcod f)) h == g)
    uC-exact-ktoi-lemma (f , fpt) (h , hpt) p =
      ((g , ! q ∙ hpt) ,
       pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (λ w → w ∙ hpt) (!-inv-r q)))
      where
      g : Cofiber f → Ω (E (succ n))
      g = CofiberRec.f f idp h (! ∘ app= (ap fst p))

      q : h (snd Y) == g (cfbase f)
      q = ap g (snd (⊙cfcod (f , fpt)))

  {- Truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- in image of (CF n (⊙cfcod f)) ⇒ in kernel of (CF n f) -}
    abstract
      C-exact-itok : (f : fst (X ⊙→ Y))
        → is-exact-itok (CF n (⊙cfcod f)) (CF n f)
      C-exact-itok f =
        itok-alt-in (CF n (⊙cfcod f)) (CF n f) (Trunc-level {n = ⟨0⟩}) $
          Trunc-elim (λ _ → =-preserves-level _ (Trunc-level {n = ⟨0⟩}))
            (ap [_] ∘ uC-exact-itok-lemma n f)

    {- in kernel of (CF n f) ⇒ in image of (CF n (⊙cfcod f)) -}
    abstract
      C-exact-ktoi : (f : fst (X ⊙→ Y))
        → is-exact-ktoi (CF n (⊙cfcod f)) (CF n f)
      C-exact-ktoi f =
        Trunc-elim
          (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
          (λ h tp → Trunc-rec Trunc-level (lemma h) (–> (Trunc=-equiv _ _) tp))
        where
        lemma : (h : uCEl n Y)
          → fst (uCF n f) h == uCid n X
          → Trunc ⟨-1⟩ (Σ (CEl n (⊙Cof f))
                          (λ tk → fst (CF n (⊙cfcod f)) tk == [ h ]))
        lemma h p = [ [ fst wit ] , ap [_] (snd wit) ]
          where
          wit : Σ (uCEl n (⊙Cof f)) (λ k → fst (uCF n (⊙cfcod f)) k == h)
          wit = uC-exact-ktoi-lemma n f h p

    C-exact : (f : fst (X ⊙→ Y)) → is-exact (CF n (⊙cfcod f)) (CF n f)
    C-exact f = record {itok = C-exact-itok f; ktoi = C-exact-ktoi f}

  {- Additivity Axiom -}
  module _ (n : ℤ) {A : Type i} (X : A → Ptd i)
    (ac : (W : A → Type i) → has-choice ⟨0⟩ A W)
    where

    uie : has-choice ⟨0⟩ A (uCEl n ∘ X)
    uie = ac (uCEl n ∘ X)

    R' : CEl n (⊙BigWedge X) → Trunc ⟨0⟩ (Π A (uCEl n ∘ X))
    R' = Trunc-rec Trunc-level (λ H → [ (λ a → H ⊙∘ ⊙bwin a) ])

    L' : Trunc ⟨0⟩ (Π A (uCEl n ∘ X)) → CEl n (⊙BigWedge X)
    L' = Trunc-rec Trunc-level
      (λ k → [ BigWedgeRec.f idp (fst ∘ k) (! ∘ snd ∘ k) , idp ])

    R = unchoose ∘ R'
    L = L' ∘ (is-equiv.g uie)

    R'-L' : ∀ y → R' (L' y) == y
    R'-L' = Trunc-elim
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
      lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
        → ! q ∙ ap f p == ! (ap f (! p) ∙ q)
      lemma f idp idp = idp

      l∘r : fst (⊙BigWedge X ⊙→ ⊙Ω (E (succ n)))
        → (BigWedge X → Ω (E (succ n)))
      l∘r (h , hpt) =
        BigWedgeRec.f idp (λ a → h ∘ bwin a)
          (λ a → ! (ap h (! (bwglue a)) ∙ hpt))

      L-R-fst : (h : fst (⊙BigWedge X ⊙→ ⊙Ω (E (succ n))))
        → ∀ w → (l∘r h) w == fst h w
      L-R-fst (h , hpt) = BigWedge-elim
        (! hpt)
        (λ _ _ → idp)
        (λ a → ↓-='-in $
           ! hpt ∙ ap h (bwglue a)
             =⟨ lemma h (bwglue a) hpt ⟩
           ! (ap h (! (bwglue a)) ∙ hpt)
             =⟨ ! (BigWedgeRec.glue-β idp (λ a → h ∘ bwin a)
                     (λ a → ! (ap h (! (bwglue a)) ∙ hpt)) a) ⟩
           ap (l∘r (h , hpt)) (bwglue a) ∎)

    R-is-equiv : is-equiv R
    R-is-equiv = uie ∘ise (is-eq R' L' R'-L' L'-R')

    pres-comp : (tf tg : CEl n (⊙BigWedge X))
      → R (Group.comp (C n (⊙BigWedge X)) tf tg)
        == Group.comp (ΠG A (C n ∘ X)) (R tf) (R tg)
    pres-comp = Trunc-elim
      (λ _ → Π-level (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level))))
      (λ {(f , fpt) → Trunc-elim
        (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
        (λ {(g , gpt) → λ= $ λ a → ap [_] $
          pair= idp (comp-snd f g (! (bwglue a)) fpt gpt)})})
      where
      comp-snd : ∀ {i j} {A : Type i} {B : Type j} {a₁ a₂ : A} {b₀ : B}
        {p q : b₀ == b₀} (f : A → b₀ == b₀) (g : A → b₀ == b₀)
        (r : a₁ == a₂) (α : f a₂ == p) (β : g a₂ == q)
        → ap (λ x → f x ∙ g x) r ∙ ap2 _∙_ α β
          == ap2 _∙_ (ap f r ∙ α) (ap g r ∙ β)
      comp-snd f g idp idp idp = idp

    abstract
      C-additive : C n (⊙BigWedge X) == ΠG A (C n ∘ X)
      C-additive = group-iso (group-hom R pres-comp) R-is-equiv

open SpectrumModel

spectrum-cohomology : CohomologyTheory i
spectrum-cohomology = record {
  C = C;
  CF-hom = CF-hom;
  CF-ident = CF-ident;
  CF-comp = CF-comp;
  C-abelian = C-abelian;
  C-Susp = C-Susp;
  C-exact = C-exact;
  C-additive = C-additive}
