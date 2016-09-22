{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Theory
open import cohomology.Choice

{- A spectrum (family (Eₙ | n : ℤ) such that ΩEₙ₊₁ = Eₙ)
 - gives rise to a cohomology theory C with Cⁿ(S⁰) = π₁(Eₙ₊₁). -}

module cohomology.SpectrumModel
  {i} (E : ℤ → Ptd i) (spectrum : (n : ℤ) → ⊙Ω (E (succ n)) ⊙≃ E n) where

module SpectrumModel where

  {- Definition of cohomology group C -}
  module _ (n : ℤ) (X : Ptd i) where
    C : Group i
    C = Trunc-⊙→Ω-group X (E (succ n))

    {- convenient abbreviations -}
    CEl = Group.El C
    ⊙CEl = Group.⊙El C
    Cid = Group.ident C

    {- before truncation -}
    uCEl = fst (X ⊙→ ⊙Ω (E (succ n)))

  {- Cⁿ(X) is an abelian group -}
  C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)
  C-abelian n X =
    iso-preserves-abelian (Trunc-⊙→Ω-group-emap-codom X (spectrum (succ n))) $
      Trunc-group-abelian (⊙→Ω-group-structure _ _) $ λ {(f , fpt) (g , gpt) →
        ⊙λ= (λ x → Ω^2-∙-comm (f x) (g x)) (pt-lemma fpt gpt)}
    where
    pt-lemma : ∀ {i} {A : Type i} {x : A} {p q : idp {a = x} == idp {a = x}}
      (α : p == idp) (β : q == idp)
      → ap (uncurry _∙_) (pair×= α β) ∙ idp
        == Ω^2-∙-comm p q ∙ ap (uncurry _∙_) (pair×= β α) ∙ idp
    pt-lemma idp idp = idp

  {- CF, the functorial action of C:
   - contravariant functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X Y : Ptd i} where

    CF-hom : fst (X ⊙→ Y) → (C n Y →ᴳ C n X)
    CF-hom f = Trunc-⊙→Ω-group-fmap-dom f (E (succ n))

    CF : fst (X ⊙→ Y) → fst (⊙CEl n Y ⊙→ ⊙CEl n X)
    CF F = GroupHom.⊙f (CF-hom F)

  {- CF-hom is a functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X : Ptd i} where

    CF-ident : CF-hom n {X} {X} (⊙idf X) == idhom (C n X)
    CF-ident = Trunc-⊙→Ω-group-fmap-dom-idf (E (succ n))

    CF-comp : {Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → CF-hom n (g ⊙∘ f) == CF-hom n f ∘ᴳ CF-hom n g
    CF-comp g f = Trunc-⊙→Ω-group-fmap-dom-∘ g f (E (succ n))

  -- Eilenberg-Steenrod Axioms

  {- Suspension Axiom -}
  private
    C-Susp' : {E₁ E₀ : Ptd i} (iso : ⊙Ω E₁ ⊙≃ E₀) (X : Ptd i)
      → Trunc-⊙→Ω-group (⊙Susp X) E₁ ≃ᴳ Trunc-⊙→Ω-group X E₀
    C-Susp' {E₁ = E₁} iso X = Trunc-⊙→Ω-group-emap-codom X iso
                          ∘eᴳ SuspAdjointLoopIso.iso X E₁

    -- This can be further simplified
    C-SuspF' : {E₁ E₀ : Ptd i} (iso : ⊙Ω E₁ ⊙≃ E₀)
      {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → fst (C-Susp' iso X) ∘ᴳ Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) E₁
        == Trunc-⊙→Ω-group-fmap-dom f E₀ ∘ᴳ fst (C-Susp' iso Y)
    C-SuspF' {E₁} {E₀} iso {X} {Y} f = group-hom= $
        ( GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso))
        ∘ GroupIso.f (SuspAdjointLoopIso.iso X E₁)
        ∘ GroupHom.f (Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) E₁)
        ) =⟨ SuspAdjointLoopIso.nat-dom f E₁
            |in-ctx GroupHom.f
            |in-ctx GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso)) ∘_ ⟩
        ( GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso))
        ∘ GroupHom.f (Trunc-⊙→Ω-group-fmap-dom f (⊙Ω E₁))
        ∘ GroupIso.f (SuspAdjointLoopIso.iso Y E₁)
        ) =⟨ ! $ Trunc-⊙→Ω-group-fmap-nat f (fst iso)
            |in-ctx GroupHom.f
            |in-ctx _∘ GroupIso.f (SuspAdjointLoopIso.iso Y E₁) ⟩
        ( GroupHom.f (Trunc-⊙→Ω-group-fmap-dom f E₀)
        ∘ GroupHom.f (Trunc-⊙→Ω-group-fmap-codom Y (fst iso))
        ∘ GroupIso.f (SuspAdjointLoopIso.iso Y E₁)
        ) =∎

  C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X
  C-Susp n X = C-Susp' (spectrum (succ n)) X

  C-SuspF : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → fst (C-Susp n X) ∘ᴳ CF-hom (succ n) (⊙Susp-fmap f)
      == CF-hom n f ∘ᴳ fst (C-Susp n Y)
  C-SuspF n f = C-SuspF' (spectrum (succ n)) f

  {- Non-truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- precomposing [⊙cfcod' f] and then [f] gives [0] -}
    exact-itok-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n (⊙Cof f))
      → (g ⊙∘ ⊙cfcod' f) ⊙∘ f == ⊙cst
    exact-itok-lemma (f , fpt) (g , gpt) = ⊙λ=
      (λ x → ap g (! (cfglue' f x)) ∙ gpt)
      (ap (g ∘ cfcod) fpt
       ∙ ap g (ap cfcod (! fpt) ∙ ! (cfglue (snd X))) ∙ gpt
         =⟨ lemma cfcod g fpt (! (cfglue (snd X))) gpt ⟩
       ap g (! (cfglue (snd X))) ∙ gpt
         =⟨ ! (∙-unit-r _) ⟩
       (ap g (! (cfglue (snd X))) ∙ gpt) ∙ idp ∎)
      where
      lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
        {a₁ a₂ : A} {b : B} {c : C} (f : A → B) (g : B → C)
        (p : a₁ == a₂) (q : f a₁ == b) (r : g b == c)
        → ap (g ∘ f) p ∙ ap g (ap f (! p) ∙ q) ∙ r == ap g q ∙ r
      lemma f g idp idp idp = idp

    {- if g ⊙∘ f is constant then g factors as h ⊙∘ ⊙cfcod' f -}
    exact-ktoi-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n Y)
      → g ⊙∘ f == ⊙cst
      → Σ (uCEl n (⊙Cof f)) (λ h → h ⊙∘ ⊙cfcod' f == g)
    exact-ktoi-lemma (f , fpt) (h , hpt) p =
      ((g , ! q ∙ hpt) ,
       pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (_∙ hpt) (!-inv-r q)))
      where
      g : Cofiber f → Ω (E (succ n))
      g = CofiberRec.f idp h (! ∘ app= (ap fst p))

      q : h (snd Y) == g (cfbase' f)
      q = ap g (snd (⊙cfcod' (f , fpt)))

  {- Truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    abstract
      C-im-sub-ker : (f : fst (X ⊙→ Y))
        → im-propᴳ (CF-hom n (⊙cfcod' f)) ⊆ᴳ ker-propᴳ (CF-hom n f)
      C-im-sub-ker f =
        im-sub-ker-in (CF-hom n (⊙cfcod' f)) (CF-hom n f) $
          Trunc-elim (λ _ → =-preserves-level _ (Trunc-level {n = 0}))
            (ap [_] ∘ exact-itok-lemma n f)

    abstract
      C-ker-sub-im : (f : fst (X ⊙→ Y))
        → ker-propᴳ (CF-hom n f) ⊆ᴳ im-propᴳ (CF-hom n (⊙cfcod' f))
      C-ker-sub-im f =
        Trunc-elim
          (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
          (λ h tp → Trunc-rec Trunc-level (lemma h) (–> (Trunc=-equiv _ _) tp))
        where
        lemma : (h : uCEl n Y) → h ⊙∘ f == ⊙cst
          → Trunc -1 (Σ (CEl n (⊙Cof f))
                          (λ tk → fst (CF n (⊙cfcod' f)) tk == [ h ]))
        lemma h p = [ [ fst wit ] , ap [_] (snd wit) ]
          where
          wit : Σ (uCEl n (⊙Cof f)) (λ k → k ⊙∘ ⊙cfcod' f == h)
          wit = exact-ktoi-lemma n f h p

    C-exact : (f : fst (X ⊙→ Y)) → is-exact (CF-hom n (⊙cfcod' f)) (CF-hom n f)
    C-exact f = record {im-sub-ker = C-im-sub-ker f; ker-sub-im = C-ker-sub-im f}

  {- Additivity Axiom -}
  module _ (n : ℤ) {A : Type i} (X : A → Ptd i)
    (ac : (W : A → Type i) → has-choice 0 A W)
    where

    into : CEl n (⊙BigWedge X) → Trunc 0 (Π A (uCEl n ∘ X))
    into = Trunc-rec Trunc-level (λ H → [ (λ a → H ⊙∘ ⊙bwin a) ])

    module Out' (K : Π A (uCEl n ∘ X)) = BigWedgeRec
      idp
      (fst ∘ K)
      (! ∘ snd ∘ K)

    out : Trunc 0 (Π A (uCEl n ∘ X)) → CEl n (⊙BigWedge X)
    out = Trunc-rec Trunc-level (λ K → [ Out'.f K , idp ])

    into-out : ∀ y → into (out y) == y
    into-out = Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ K → ap [_] (λ= (λ a → pair= idp $
        ap (Out'.f K) (! (bwglue a)) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap (Out'.f K) (! (bwglue a))
          =⟨ ap-! (Out'.f K) (bwglue a) ⟩
        ! (ap (Out'.f K) (bwglue a))
          =⟨ ap ! (Out'.glue-β K a) ⟩
        ! (! (snd (K a)))
          =⟨ !-! (snd (K a)) ⟩
        snd (K a) ∎)))

    out-into : ∀ x → out (into x) == x
    out-into = Trunc-elim
      {P = λ tH → out (into tH) == tH}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ {(h , hpt) → ap [_] $ pair=
         (λ= (out-into-fst (h , hpt)))
         (↓-app=cst-in $ ! $
            ap (λ w → w ∙ hpt) (app=-β (out-into-fst (h , hpt)) bwbase)
            ∙ !-inv-l hpt)})
      where
      lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
        → ! q ∙ ap f p == ! (ap f (! p) ∙ q)
      lemma f idp idp = idp

      out-into-fst : (H : fst (⊙BigWedge X ⊙→ ⊙Ω (E (succ n))))
        → ∀ w → Out'.f (λ a → H ⊙∘ ⊙bwin a) w == fst H w
      out-into-fst (h , hpt) = BigWedge-elim
        (! hpt)
        (λ _ _ → idp)
        (λ a → ↓-='-in $
           ! hpt ∙ ap h (bwglue a)
             =⟨ lemma h (bwglue a) hpt ⟩
           ! (ap h (! (bwglue a)) ∙ hpt)
             =⟨ ! (Out'.glue-β (λ a → (h , hpt) ⊙∘ ⊙bwin a) a) ⟩
           ap (Out'.f (λ a → (h , hpt) ⊙∘ ⊙bwin a)) (bwglue a) ∎)

    abstract
      C-additive : is-equiv (GroupHom.f (Πᴳ-fanout (CF-hom n ∘ ⊙bwin {X = X})))
      C-additive = transport is-equiv
        (λ= $ Trunc-elim
          (λ _ → =-preserves-level _ $ Π-level $ λ _ → Trunc-level)
          (λ _ → idp))
        ((ac (uCEl n ∘ X)) ∘ise (is-eq into out into-out out-into))


open SpectrumModel

spectrum-cohomology : CohomologyTheory i
spectrum-cohomology = record {
  C = C;
  CF-hom = CF-hom;
  CF-ident = CF-ident;
  CF-comp = CF-comp;
  C-abelian = C-abelian;
  C-Susp = C-Susp;
  C-SuspF = C-SuspF;
  C-exact = C-exact;
  C-additive = C-additive}

spectrum-C-S⁰ : (n : ℤ) → C n (⊙Lift ⊙S⁰) ≃ᴳ πS 0 (E (succ n))
spectrum-C-S⁰ n = Trunc-⊙Bool→Ω-iso-π₁ (E (succ n)) ∘eᴳ Trunc-⊙→Ω-group-emap-dom ⊙lift-equiv (E (succ n))
