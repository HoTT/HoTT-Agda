{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.SumOfSubIndicator
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

      inverse-C-subfinite-additive-β' : ∀ {A B : Type₀} (B-dec : has-dec-eq B) {I}
        (p : Fin I ≃ Coprod A B) {X : Ptd₀}
        → ∀ f → GroupHom.f (C-subfinite-additive (–> p) X) (explicit-inverse-C-subfinite-additive (–> p) X B-dec f) ∼ f
      inverse-C-subfinite-additive-β' B-dec p {X} f b* =
        CEl-fmap n (⊙bwin b*) (Group.subsum-r (C n (⊙BigWedge (λ _ → X))) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b) (f b)))
          =⟨ GroupHom.pres-subsum-r (C-fmap n (⊙bwin b*)) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b) (f b)) ⟩
        Group.subsum-r (C n X) (–> p) (λ b → CEl-fmap n (⊙bwin b*) (CEl-fmap n (⊙bwproj B-dec b) (f b)))
          =⟨ ap (Group.subsum-r (C n X) (–> p)) (λ= λ b → ∘-CEl-fmap n (⊙bwin b*) (⊙bwproj B-dec b) (f b)) ⟩
        Group.subsum-r (C n X) (–> p) (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin b*) (f b))
          =⟨ subsum-r-subindicator (C n X) p (λ b → CEl-fmap n (⊙bwproj B-dec b ⊙∘ ⊙bwin b*) (f b))
              b* (λ b≠b* → C-bwproj-bwin-≠ B-dec b≠b* _) ⟩
        CEl-fmap n (⊙bwproj B-dec b* ⊙∘ ⊙bwin b*) (f b*)
          =⟨ C-bwproj-bwin-diag B-dec b* (f b*) ⟩
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
