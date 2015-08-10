{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients
open import cohomology.Theory
open import cohomology.Exactness
open import cohomology.Choice

{- A spectrum (family (Eₙ | n : ℤ) such that ΩEₙ₊₁ = Eₙ)
 - gives rise to a cohomology theory C with Cⁿ(S⁰) = π₁(Eₙ₊₁). -}

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
    uCEl = fst (X ⊙→ ⊙Ω (E (succ n)))

  {- Cⁿ(X) is an abelian group -}
  C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)
  C-abelian n X =
    transport (is-abelian ∘ →Ω-Group X) (spectrum (succ n)) $
      Trunc-Group-abelian (→Ω-group-structure _ _) $ λ {(f , fpt) (g , gpt) →
        ⊙λ= (λ x → conc^2-comm (f x) (g x)) (pt-lemma fpt gpt)}
    where
    pt-lemma : ∀ {i} {A : Type i} {x : A} {p q : idp {a = x} == idp {a = x}}
      (α : p == idp) (β : q == idp)
      → ap (uncurry _∙_) (ap2 _,_ α β) ∙ idp
        == conc^2-comm p q ∙ ap (uncurry _∙_) (ap2 _,_ β α) ∙ idp
    pt-lemma idp idp = idp

  {- CF, the functorial action of C:
   - contravariant functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X Y : Ptd i} where

    CF-hom : fst (X ⊙→ Y) → (C n Y →ᴳ C n X)
    CF-hom f = →Ω-Group-dom-act f (E (succ n))

    CF : fst (X ⊙→ Y) → fst (⊙CEl n Y ⊙→ ⊙CEl n X)
    CF F = GroupHom.⊙f (CF-hom F)

  {- CF-hom is a functor from pointed spaces to abelian groups -}
  module _ (n : ℤ) {X : Ptd i} where

    CF-ident : CF-hom n {X} {X} (⊙idf X) == idhom (C n X)
    CF-ident = →Ω-Group-dom-idf (E (succ n))

    CF-comp : {Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → CF-hom n (g ⊙∘ f) == CF-hom n f ∘ᴳ CF-hom n g
    CF-comp g f = →Ω-Group-dom-∘ g f (E (succ n))

  -- Eilenberg-Steenrod Axioms

  {- Suspension Axiom -}
  private
    C-Susp' : {E₁ E₀ : Ptd i} (p : ⊙Ω E₁ == E₀) (X : Ptd i)
      → →Ω-Group (⊙Susp X) E₁ ≃ᴳ →Ω-Group X E₀
    C-Susp' {E₁ = E₁} idp X = SuspAdjointLoopIso.iso X E₁

    C-SuspF' : {E₁ E₀ : Ptd i} (p : ⊙Ω E₁ == E₀)
      {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → fst (C-Susp' p X) ∘ᴳ →Ω-Group-dom-act (⊙susp-fmap f) E₁
        == →Ω-Group-dom-act f E₀ ∘ᴳ fst (C-Susp' p Y)
    C-SuspF' {E₁ = E₁} idp f = SuspAdjointLoopIso.nat-dom f E₁

  C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (⊙Susp X) ≃ᴳ C n X
  C-Susp n X = C-Susp' (spectrum (succ n)) X

  C-SuspF : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → fst (C-Susp n X) ∘ᴳ CF-hom (succ n) (⊙susp-fmap f)
      == CF-hom n f ∘ᴳ fst (C-Susp n Y)
  C-SuspF n f = C-SuspF' (spectrum (succ n)) f

  {- Non-truncated Exactness Axiom -}
  module _ (n : ℤ) {X Y : Ptd i} where

    {- precomposing ⊙cfcod f and then f gives 0 -}
    exact-itok-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n (⊙Cof f))
      → (g ⊙∘ ⊙cfcod f) ⊙∘ f == ⊙cst
    exact-itok-lemma (f , fpt) (g , gpt) = ⊙λ=
      (λ x → ap g (! (cfglue f x)) ∙ gpt)
      (ap (g ∘ cfcod f) fpt
       ∙ ap g (ap (cfcod f) (! fpt) ∙ ! (cfglue f (snd X))) ∙ gpt
         =⟨ lemma (cfcod f) g fpt (! (cfglue f (snd X))) gpt ⟩
       ap g (! (cfglue f (snd X))) ∙ gpt
         =⟨ ! (∙-unit-r _) ⟩
       (ap g (! (cfglue f (snd X))) ∙ gpt) ∙ idp ∎)
      where
      lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
        {a₁ a₂ : A} {b : B} {c : C} (f : A → B) (g : B → C)
        (p : a₁ == a₂) (q : f a₁ == b) (r : g b == c)
        → ap (g ∘ f) p ∙ ap g (ap f (! p) ∙ q) ∙ r == ap g q ∙ r
      lemma f g idp idp idp = idp

    {- if g ⊙∘ f is constant then g factors as h ⊙∘ ⊙cfcod f -}
    exact-ktoi-lemma : (f : fst (X ⊙→ Y)) (g : uCEl n Y)
      → g ⊙∘ f == ⊙cst
      → Σ (uCEl n (⊙Cof f)) (λ h → h ⊙∘ ⊙cfcod f == g)
    exact-ktoi-lemma (f , fpt) (h , hpt) p =
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
        → is-exact-itok (CF-hom n (⊙cfcod f)) (CF-hom n f)
      C-exact-itok f =
        itok-alt-in (CF-hom n (⊙cfcod f)) (CF-hom n f) $
          Trunc-elim (λ _ → =-preserves-level _ (Trunc-level {n = ⟨0⟩}))
            (ap [_] ∘ exact-itok-lemma n f)

    {- in kernel of (CF n f) ⇒ in image of (CF n (⊙cfcod f)) -}
    abstract
      C-exact-ktoi : (f : fst (X ⊙→ Y))
        → is-exact-ktoi (CF-hom n (⊙cfcod f)) (CF-hom n f)
      C-exact-ktoi f =
        Trunc-elim
          (λ _ → Π-level (λ _ → raise-level _ Trunc-level))
          (λ h tp → Trunc-rec Trunc-level (lemma h) (–> (Trunc=-equiv _ _) tp))
        where
        lemma : (h : uCEl n Y) → h ⊙∘ f == ⊙cst
          → Trunc ⟨-1⟩ (Σ (CEl n (⊙Cof f))
                          (λ tk → fst (CF n (⊙cfcod f)) tk == [ h ]))
        lemma h p = [ [ fst wit ] , ap [_] (snd wit) ]
          where
          wit : Σ (uCEl n (⊙Cof f)) (λ k → k ⊙∘ ⊙cfcod f == h)
          wit = exact-ktoi-lemma n f h p

    C-exact : (f : fst (X ⊙→ Y)) → is-exact (CF-hom n (⊙cfcod f)) (CF-hom n f)
    C-exact f = record {itok = C-exact-itok f; ktoi = C-exact-ktoi f}

  {- Additivity Axiom -}
  module _ (n : ℤ) {A : Type i} (X : A → Ptd i)
    (ac : (W : A → Type i) → has-choice ⟨0⟩ A W)
    where

    into : CEl n (⊙BigWedge X) → Trunc ⟨0⟩ (Π A (uCEl n ∘ X))
    into = Trunc-rec Trunc-level (λ H → [ (λ a → H ⊙∘ ⊙bwin a) ])

    module Out' (K : Π A (uCEl n ∘ X)) = BigWedgeRec
      idp
      (fst ∘ K)
      (! ∘ snd ∘ K)

    out : Trunc ⟨0⟩ (Π A (uCEl n ∘ X)) → CEl n (⊙BigWedge X)
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
      C-additive : is-equiv (GroupHom.f (Πᴳ-hom-in (CF-hom n ∘ ⊙bwin {X = X})))
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

spectrum-C-S⁰ : (n : ℤ) → C n (⊙Sphere O) == π 1 (ℕ-S≠O _) (E (succ n))
spectrum-C-S⁰ n = Bool⊙→Ω-is-π₁ (E (succ n))
