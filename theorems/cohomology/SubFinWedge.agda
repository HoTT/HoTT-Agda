{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

{- It should be possible to prove lemmas for arbitrary universe levels,
   but this file is only used for [FinSkeleton], which is in the zeroth
   universe. -}

module cohomology.SubFinWedge (CT : CohomologyTheory lzero) (n : ℤ) where

open CohomologyTheory CT

{-
  [B-ac] and [B-dec] can actually be proved from [subfin],
  but maybe the user wants to supply a different [B-ac].

  Another good question is why the focus is on [B], not [A].
  Well, check the definition of [MinusPoint] and you will see why.
-}

module _ {I} {A B : Type₀} (p : Fin I → Coprod A B) (X : Ptd₀) where

  C-subfinite-additive : C n (⊙BigWedge (λ (_ : B) → X)) →ᴳ Πᴳ B (λ _ → C n X)
  C-subfinite-additive = C-additive n (λ (_ : B) → X)

  CEl-subfinite-additive : CEl n (⊙BigWedge (λ (_ : B) → X)) → Π B (λ _ → CEl n X)
  CEl-subfinite-additive = GroupHom.f C-subfinite-additive

  C-subfinite-additive-is-equiv : has-choice 0 B lzero → is-equiv CEl-subfinite-additive
  C-subfinite-additive-is-equiv = C-additive-is-equiv n (λ _ → X)

  C-subfinite-additive-iso : has-choice 0 B lzero
    → C n (⊙BigWedge (λ (_ : B) → X)) ≃ᴳ Πᴳ B (λ _ → C n X)
  C-subfinite-additive-iso = C-additive-iso n (λ (_ : B) → X)

  {- an explicit inverse function -}
  explicit-inverse-C-subfinite-additive : has-dec-eq B
    → Π B (λ _ → CEl n X) → CEl n (⊙BigWedge (λ (_ : B) → X))
  explicit-inverse-C-subfinite-additive B-dec f =
    Group.subsum-r (C n (⊙BigWedge (λ _ → X))) p (λ b → CEl-fmap n (⊙bwproj B-dec b) (f b))

module _ where
  
  {- this part is to prove the explicit inverse function is correct -}
  abstract
    private
      C-bwproj-bwin-≠ : {B : Type₀} (B-dec : has-dec-eq B) {X : Ptd₀}
        {b b' : B} (neq : b ≠ b') (g : CEl n X)
        → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b') g == Cident n X
      C-bwproj-bwin-≠ B-dec neq g =
        CEl-fmap-base-indep n (bwproj-bwin-≠ B-dec neq) g ∙ C-fmap-cst n g

      C-bwproj-bwin-diag : {B : Type₀} (B-dec : has-dec-eq B) {X : Ptd₀} (b : B) (g : CEl n X)
        → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b) g == g
      C-bwproj-bwin-diag B-dec b g =
        CEl-fmap-base-indep n (bwproj-bwin-diag B-dec b) g ∙ C-fmap-idf n g

      subsum-r-C-bwproj-bwin-late' : ∀ {A B : Type₀} (B-dec : has-dec-eq B) m o {I}
        (p : Fin (ℕ-S^' (S m) (ℕ-S^' o I)) ≃ Coprod A B) {X : Ptd₀} (f : Π B (λ _ → CEl n X)) {b*}
        → inr b* == –> p (Fin-S^' m (ℕ-S^' o I , ltS))
        → Group.subsum-r (C n X) (–> p ∘ Fin-S^' (S m) ∘ Fin-S^' o)
            (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b*) (f b))
        == Cident n X
      subsum-r-C-bwproj-bwin-late' B-dec m o {I = O} p {X} f _ = idp
      subsum-r-C-bwproj-bwin-late' B-dec m o {I = S I} p {X} f {b*} path₀ =
        ap2 (Group.comp (C n X))
          (subsum-r-C-bwproj-bwin-late' B-dec m (S o) p {X} f path₀)
          (Coprod-elim
            {C = λ c →
              c == –> p (Fin-S^' (S m) (Fin-S^' o (I , ltS)))
              →  Coprod-rec (λ _ → Cident n X)
                 (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b*) (f b))
                 c
              == Cident n X}
            (λ _ _ → idp)
            (λ b path₁ → C-bwproj-bwin-≠ B-dec (λ b=b* → –>-≠ p (Fin-S^'-≠ m (ltSR≠ltS _)) (! path₁ ∙ ap inr b=b* ∙' path₀)) _)
            (–> p (Fin-S^' (S m) (Fin-S^' o (I , ltS)))) idp)
        ∙ Group.unit-l (C n X) _

      subsum-C-bwproj-bwin' : ∀ {A B : Type₀} (B-dec : has-dec-eq B) m {I}
        (p : Fin (ℕ-S^' m I) ≃ Coprod A B) {X : Ptd₀} (f : Π B (λ _ → CEl n X)) {b*}
        → (<I* : Fin I) → inr b* == –> p (Fin-S^' m <I*)
        → Group.subsum-r (C n X) (–> p ∘ Fin-S^' m)
            (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b*) (f b))
        == f b*
      subsum-C-bwproj-bwin' B-dec m p {X} f {b*} (I , ltS) path₀ =
        ap2 (Group.comp (C n X))
          (subsum-r-C-bwproj-bwin-late' B-dec m 0 {I = I} p {X} f {b*} path₀)
          ( ap
              (Coprod-rec
                (λ _ → Cident n X)
                (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b*) (f b)))
              (! path₀)
          ∙ C-bwproj-bwin-diag B-dec b* (f b*))
        ∙ Group.unit-l (C n X) _
      subsum-C-bwproj-bwin' B-dec m {I = S I} p {X} f {b*} (o , ltSR o<I) path₀ =
        ap2 (Group.comp (C n X))
          (subsum-C-bwproj-bwin' B-dec (S m) {I} p {X} f (o , o<I) path₀)
          (Coprod-elim
            {C = λ c →
              c == –> p (Fin-S^' m (I , ltS))
              →  Coprod-rec (λ _ → Cident n X)
                 (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin {X = λ _ → X} b*) (f b))
                 c
              == Cident n X}
            (λ _ _ → idp)
            (λ b path₁ → C-bwproj-bwin-≠ B-dec (λ b=b* → –>-≠ p (Fin-S^'-≠ m (ltS≠ltSR _)) (! path₁ ∙ ap inr b=b* ∙' path₀)) _)
            (–> p (Fin-S^' m (I , ltS))) idp)
        ∙ Group.unit-r (C n X) _

      inverse-C-subfinite-additive-β' : ∀ {A B : Type₀} (B-dec : has-dec-eq B) {I}
        (p : Fin I ≃ Coprod A B) {X : Ptd₀}
        → ∀ f → GroupHom.f (C-subfinite-additive (–> p) X) (explicit-inverse-C-subfinite-additive (–> p) X B-dec f) ∼ f
      inverse-C-subfinite-additive-β' B-dec p {X} f b* =
        CEl-fmap n (⊙bwin b*) (Group.subsum-r (C n (⊙BigWedge (λ _ → X))) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b) (f b)))
          =⟨ GroupHom.pres-subsum-r (C-fmap n (⊙bwin b*)) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b) (f b)) ⟩
        Group.subsum-r (C n X) (–> p) (λ b → CEl-fmap n (⊙bwin b*) (CEl-fmap n (⊙bwproj B-dec b) (f b)))
          =⟨ ap (Group.subsum-r (C n X) (–> p)) (λ= λ b → ∘-CEl-fmap n (⊙bwin b*) (⊙bwproj B-dec b) (f b)) ⟩
        Group.subsum-r (C n X) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin b*) (f b))
          =⟨ subsum-C-bwproj-bwin' B-dec 0 p f (<– p (inr b*)) (! $ <–-inv-r p (inr b*)) ⟩
        f b*
          =∎

    inverse-C-subfinite-additive-β : ∀ {A B : Type₀}
      (B-ac : has-choice 0 B lzero) (B-dec : has-dec-eq B) {I}
      (p : Fin I ≃ Coprod A B) {X : Ptd₀}
      → is-equiv.g (C-subfinite-additive-is-equiv (–> p) X B-ac)
      ∼ explicit-inverse-C-subfinite-additive (–> p) X B-dec
    inverse-C-subfinite-additive-β B-ac B-dec p {X} f =
      ! $ equiv-adj (GroupIso.f-equiv (C-subfinite-additive-iso (–> p) X B-ac)) $
        λ= $ inverse-C-subfinite-additive-β' B-dec p f

module _ (I : ℕ) (X : Ptd₀) where

  C-finite-additive : C n (⊙BigWedge (λ (_ : Fin I) → X)) →ᴳ Πᴳ (Fin I) (λ _ → C n X)
  C-finite-additive = C-subfinite-additive {A = Empty} inr X 

  CEl-finite-additive : CEl n (⊙BigWedge (λ (_ : Fin I) → X)) → Π (Fin I) (λ _ → CEl n X)
  CEl-finite-additive = GroupHom.f C-finite-additive

  C-finite-additive-is-equiv : is-equiv CEl-finite-additive
  C-finite-additive-is-equiv = C-subfinite-additive-is-equiv {A = Empty} inr X (Fin-has-choice 0 lzero)

  C-finite-additive-iso : C n (⊙BigWedge (λ (_ : Fin I) → X)) ≃ᴳ Πᴳ (Fin I) (λ _ → C n X)
  C-finite-additive-iso = C-subfinite-additive-iso {A = Empty} inr X (Fin-has-choice 0 lzero)

  {- an explicit inverse function -}
  explicit-inverse-C-finite-additive : Π (Fin I) (λ _ → CEl n X) → CEl n (⊙BigWedge (λ (_ : Fin I) → X))
  explicit-inverse-C-finite-additive = explicit-inverse-C-subfinite-additive {A = Empty} inr X Fin-has-dec-eq
    
module _ where
  abstract
    inverse-C-finite-additive-β : ∀ {I : ℕ} {X : Ptd₀}
      → is-equiv.g (C-finite-additive-is-equiv I X)
      ∼ explicit-inverse-C-finite-additive I X
    inverse-C-finite-additive-β {I} {X} =
      inverse-C-subfinite-additive-β {A = Empty} {B = Fin I}
        (Fin-has-choice 0 lzero) Fin-has-dec-eq (⊔₁-Empty (Fin I) ⁻¹) {X}
