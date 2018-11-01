{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.SuspAdjointLoop
open import groups.ToOmega
open import cohomology.Theory

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
    uCEl = X ⊙→ ⊙Ω (E (succ n))

  {- Cⁿ(X) is an abelian group -}
  C-is-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)
  C-is-abelian n X =
    iso-preserves-abelian (Trunc-⊙→Ω-group-emap-codom X (spectrum (succ n))) $
      Trunc-group-abelian (⊙→Ω-group-structure _ _) $ λ {(f , fpt) (g , gpt) →
        ⊙λ=' (λ x → Ω^2-∙-comm (f x) (g x)) (pt-lemma fpt gpt)}
    where
    pt-lemma : ∀ {i} {A : Type i} {x : A} {p q : idp {a = x} == idp {a = x}}
      (α : p == idp) (β : q == idp)
      →  ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α β) idp
      == ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt β α) idp
       [ _== idp ↓ Ω^2-∙-comm p q ]
    pt-lemma idp idp = idp

  {- C-fmap, the functorial action of C:
   - contravariant functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X Y : Ptd i} where

    C-fmap : X ⊙→ Y → (C n Y →ᴳ C n X)
    C-fmap f = Trunc-⊙→Ω-group-fmap-dom f (E (succ n))

    CEl-fmap : X ⊙→ Y → CEl n Y → CEl n X
    CEl-fmap F = GroupHom.f (C-fmap F)

    ⊙CEl-fmap : X ⊙→ Y → ⊙CEl n Y ⊙→ ⊙CEl n X
    ⊙CEl-fmap F = GroupHom.⊙f (C-fmap F)

  {- C-fmap is a functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X : Ptd i} where

    C-fmap-idf : ∀ x → CEl-fmap n {X} {X} (⊙idf X) x == x
    C-fmap-idf x = ap (λ h → GroupHom.f h x) (Trunc-⊙→Ω-group-fmap-dom-idf (E (succ n)))

    C-fmap-∘ : {Y Z : Ptd i} (g : Y ⊙→ Z) (f : X ⊙→ Y)
      → ∀ x → CEl-fmap n (g ⊙∘ f) x == CEl-fmap n f (CEl-fmap n g x)
    C-fmap-∘ g f x = ap (λ h → GroupHom.f h x) (Trunc-⊙→Ω-group-fmap-dom-∘ g f (E (succ n)))

  -- Eilenberg-Steenrod Axioms

  {- Susp Axiom -}
  private
    C-Susp' : {E₁ E₀ : Ptd i} (iso : ⊙Ω E₁ ⊙≃ E₀) (X : Ptd i)
      → Trunc-⊙→Ω-group (⊙Susp X) E₁ ≃ᴳ Trunc-⊙→Ω-group X E₀
    C-Susp' {E₁ = E₁} iso X = Trunc-⊙→Ω-group-emap-codom X iso
                          ∘eᴳ Trunc-⊙→Ω-iso-Trunc-⊙→Ω X E₁

    -- This can be further simplified
    C-Susp-fmap' : {E₁ E₀ : Ptd i} (iso : ⊙Ω E₁ ⊙≃ E₀) {X Y : Ptd i} (f : X ⊙→ Y)
      → CommSquareᴳ
          (Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) E₁)
          (Trunc-⊙→Ω-group-fmap-dom f E₀)
          (fst (C-Susp' iso Y)) (fst (C-Susp' iso X))
    C-Susp-fmap' {E₁} {E₀} iso {X} {Y} f = comm-sqrᴳ λ x →
        GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso))
          (GroupIso.f (Trunc-⊙→Ω-iso-Trunc-⊙→Ω X E₁)
            (GroupHom.f (Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) E₁) x))
          =⟨ Trunc-⊙→Ω-iso-Trunc-⊙→Ω-nat-dom f E₁
            |in-ctx (λ h → GroupHom.f h x)
            |in-ctx GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso)) ⟩
        GroupHom.f (Trunc-⊙→Ω-group-fmap-codom X (fst iso))
          (GroupHom.f (Trunc-⊙→Ω-group-fmap-dom f (⊙Ω E₁))
            (GroupIso.f (Trunc-⊙→Ω-iso-Trunc-⊙→Ω Y E₁) x))
          =⟨ ! $ Trunc-⊙→Ω-group-fmap-nat f (fst iso)
            |in-ctx GroupHom.f
            |in-ctx (λ h → h (GroupIso.f (Trunc-⊙→Ω-iso-Trunc-⊙→Ω Y E₁) x)) ⟩
        GroupHom.f (Trunc-⊙→Ω-group-fmap-dom f E₀)
          (GroupHom.f (Trunc-⊙→Ω-group-fmap-codom Y (fst iso))
            (GroupIso.f (Trunc-⊙→Ω-iso-Trunc-⊙→Ω Y E₁) x))
          =∎

  C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X
  C-Susp n X = C-Susp' (spectrum (succ n)) X

  C-Susp-fmap : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y)
    → CommSquareᴳ
        (C-fmap (succ n) (⊙Susp-fmap f)) (C-fmap n f)
        (fst (C-Susp n Y)) (fst (C-Susp n X))
  C-Susp-fmap n f = C-Susp-fmap' (spectrum (succ n)) f

  {- Non-truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- precomposing [⊙cfcod' f] and then [f] gives [0] -}
    im-sub-ker-lemma : (f : X ⊙→ Y) (g : uCEl n (⊙Cofiber f))
      → (g ⊙∘ ⊙cfcod' f) ⊙∘ f == ⊙cst
    im-sub-ker-lemma (f , fpt) (g , gpt) = ⊙λ='
      (λ x → ap g (! (cfglue' f x)) ∙ gpt)
      (↓-idf=cst-in
        (ap (g ∘ cfcod) fpt
         ∙ ap g (ap cfcod (! fpt) ∙ ! (cfglue (pt X))) ∙ gpt
           =⟨ lemma cfcod g fpt (! (cfglue (pt X))) gpt ⟩
         ap g (! (cfglue (pt X))) ∙ gpt
           =⟨ ! (∙-unit-r _) ⟩
         (ap g (! (cfglue (pt X))) ∙ gpt) ∙ idp ∎))
      where
      lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
        {a₁ a₂ : A} {b : B} {c : C} (f : A → B) (g : B → C)
        (p : a₁ == a₂) (q : f a₁ == b) (r : g b == c)
        → ap (g ∘ f) p ∙ ap g (ap f (! p) ∙ q) ∙ r == ap g q ∙ r
      lemma f g idp idp idp = idp

    {- if g ⊙∘ f is constant then g factors as h ⊙∘ ⊙cfcod' f -}
    ker-sub-im-lemma : (f : X ⊙→ Y) (g : uCEl n Y)
      → g ⊙∘ f == ⊙cst
      → Σ (uCEl n (⊙Cofiber f)) (λ h → h ⊙∘ ⊙cfcod' f == g)
    ker-sub-im-lemma (f , fpt) (h , hpt) p =
      ((g , ! q ∙ hpt) ,
       pair= idp (! (∙-assoc q (! q) hpt) ∙ ap (_∙ hpt) (!-inv-r q)))
      where
      g : Cofiber f → Ω (E (succ n))
      g = CofiberRec.f idp h (! ∘ app= (ap fst p))

      q : h (pt Y) == g (cfbase' f)
      q = ap g (snd (⊙cfcod' (f , fpt)))

  {- Truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    abstract
      C-im-sub-ker : (f : X ⊙→ Y)
        → im-propᴳ (C-fmap n (⊙cfcod' f)) ⊆ᴳ ker-propᴳ (C-fmap n f)
      C-im-sub-ker f =
        im-sub-ker-in (C-fmap n (⊙cfcod' f)) (C-fmap n f) $
          Trunc-elim
            (ap [_] ∘ im-sub-ker-lemma n f)

    abstract
      C-ker-sub-im : (f : X ⊙→ Y)
        → ker-propᴳ (C-fmap n f) ⊆ᴳ im-propᴳ (C-fmap n (⊙cfcod' f))
      C-ker-sub-im f =
        Trunc-elim
          {{λ _ → Π-level (λ _ → raise-level _ Trunc-level)}}
          (λ h tp → Trunc-rec (lemma h) (–> (=ₜ-equiv _ _) tp))
        where
        lemma : (h : uCEl n Y) → h ⊙∘ f == ⊙cst
          → Trunc -1 (Σ (CEl n (⊙Cofiber f))
                          (λ tk → fst (⊙CEl-fmap n (⊙cfcod' f)) tk == [ h ]))
        lemma h p = [ [ fst wit ] , ap [_] (snd wit) ]
          where
          wit : Σ (uCEl n (⊙Cofiber f)) (λ k → k ⊙∘ ⊙cfcod' f == h)
          wit = ker-sub-im-lemma n f h p

    C-exact : (f : X ⊙→ Y) → is-exact (C-fmap n (⊙cfcod' f)) (C-fmap n f)
    C-exact f = record {im-sub-ker = C-im-sub-ker f; ker-sub-im = C-ker-sub-im f}

  {- Additivity Axiom -}
  module _ (n : ℤ) {A : Type i} (X : A → Ptd i)
    (ac : has-choice 0 A i)
    where

    into : CEl n (⊙BigWedge X) → Trunc 0 (Π A (uCEl n ∘ X))
    into = Trunc-rec (λ H → [ (λ a → H ⊙∘ ⊙bwin a) ])

    module Out' (K : Π A (uCEl n ∘ X)) = BigWedgeRec
      idp
      (fst ∘ K)
      (! ∘ snd ∘ K)

    out : Trunc 0 (Π A (uCEl n ∘ X)) → CEl n (⊙BigWedge X)
    out = Trunc-rec (λ K → [ Out'.f K , idp ])

    into-out : ∀ y → into (out y) == y
    into-out = Trunc-elim
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
      (λ {(h , hpt) → ap [_] $ ⊙λ=' (out-into-fst (h , hpt)) (↓-idf=cst-in (! (!-inv-l hpt)))})
      where
      lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {a₁ a₂ : A} {b : B} (p : a₁ == a₂) (q : f a₁ == b)
        → ! q ∙ ap f p == ! (ap f (! p) ∙ q)
      lemma f idp idp = idp

      out-into-fst : (H : ⊙BigWedge X ⊙→ ⊙Ω (E (succ n)))
        → ∀ w → Out'.f (λ a → H ⊙∘ ⊙bwin a) w == fst H w
      out-into-fst (h , hpt) = BigWedge-elim
        (! hpt)
        (λ _ _ → idp)
        (λ a → ↓-='-in' $
           ! hpt ∙ ap h (bwglue a)
             =⟨ lemma h (bwglue a) hpt ⟩
           ! (ap h (! (bwglue a)) ∙ hpt)
             =⟨ ! (Out'.glue-β (λ a → (h , hpt) ⊙∘ ⊙bwin a) a) ⟩
           ap (Out'.f (λ a → (h , hpt) ⊙∘ ⊙bwin a)) (bwglue a) ∎)

    abstract
      C-additive-is-equiv : is-equiv (GroupHom.f (Πᴳ-fanout (C-fmap n ∘ ⊙bwin {X = X})))
      C-additive-is-equiv =
        transport is-equiv
          {x = unchoose ∘ into}
          {y = GroupHom.f (Πᴳ-fanout (C-fmap n ∘ ⊙bwin {X = X}))}
          (λ= $ Trunc-elim (λ _ → idp))
          (ac (uCEl n ∘ X) ∘ise (is-eq into out into-out out-into))

open SpectrumModel

spectrum-cohomology : CohomologyTheory i
spectrum-cohomology = record {
  C = C;
  C-fmap = C-fmap;
  C-fmap-idf = C-fmap-idf;
  C-fmap-∘ = C-fmap-∘;
  C-is-abelian = C-is-abelian;
  C-Susp = C-Susp;
  C-Susp-fmap = C-Susp-fmap;
  C-exact = C-exact;
  C-additive-is-equiv = C-additive-is-equiv}

spectrum-C-S⁰ : (n : ℤ) → C n (⊙Lift ⊙S⁰) ≃ᴳ πS 0 (E (succ n))
spectrum-C-S⁰ n = Trunc-⊙Bool→Ω-iso-π₁ (E (succ n)) ∘eᴳ Trunc-⊙→Ω-group-emap-dom ⊙lift-equiv (E (succ n))
