{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge
open import cohomology.Theory
open import groups.FinProduct 

{- It should be possible to prove lemmas for arbitrary universe levels,
   but this file is only used for [FinSkeleton], which is in the 0th
   universe. -}

module cohomology.FinWedge (CT : CohomologyTheory lzero) (n : ℤ) where

open CohomologyTheory CT

module _ {I} (Z : Fin I → Ptd₀) where

  C-finite-additive : is-equiv (GroupHom.f (C-additive-hom n Z))
  C-finite-additive = C-additive n Z (Fin-has-choice 0 I lzero)

  C-finite-additive-iso : C n (⊙FinWedge Z) ≃ᴳ Πᴳ (Fin I) (C n ∘ Z)
  C-finite-additive-iso = C-additive-iso n Z (Fin-has-choice 0 I lzero)

  {- an explicit inverse function -}
  inverse-C-finite-additive :
    Π (Fin I) (CEl n ∘ Z) → CEl n (⊙FinWedge Z)
  inverse-C-finite-additive f =
    Group.sum (C n (⊙FinWedge Z)) (λ <I → CEl-fmap n (⊙fwproj <I) (f <I))

module _ where
  
  {- this part is to prove the explicit inverse function is correct -}
  private
    C-fwproj-fwin-late : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) <I g
      →  CEl-fmap n (⊙fwproj (Fin-S^' (S m) <I) ⊙∘ ⊙fwin {X = Z} (Fin-S^' m (I , ltS))) g
      == Cident n (Z (Fin-S^' m (I , ltS)))
    C-fwproj-fwin-late m Z <I g =
      CEl-fmap-base-indep n (fwproj-fwin-early m <I) g ∙ C-fmap-cst n g

    C-fwproj-fwin-early : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) <I g
      →  CEl-fmap n (⊙fwproj (Fin-S^' m (I , ltS)) ⊙∘ ⊙fwin {X = Z} (Fin-S^' (S m) <I)) g
      == Cident n (Z (Fin-S^' (S m) <I))
    C-fwproj-fwin-early m Z <I g =
      CEl-fmap-base-indep n (fwproj-fwin-late m <I) g ∙ C-fmap-cst n g

    C-fwproj-fwin-diag : ∀ {I} (Z : Fin I → Ptd₀) <I g
      → CEl-fmap n (⊙fwproj <I ⊙∘ ⊙fwin {X = Z} <I) g == g
    C-fwproj-fwin-diag Z <I g =
      CEl-fmap-base-indep n (fwproj-fwin-diag <I) g ∙ C-fmap-idf n g

    sum-C-fwproj-fwin-late' : ∀ m o {I} (Z : Fin (ℕ-S^' (S m) (ℕ-S^' o I)) → Ptd₀) (f : Π _ (CEl n ∘ Z))
      →  Group.sum (C n (Z (Fin-S^' m (ℕ-S^' o I , ltS))))
           (λ <I' → CEl-fmap n
                (⊙fwproj (Fin-S^' (S m) (Fin-S^' o <I')) ⊙∘ ⊙fwin {X = Z} (Fin-S^' m (ℕ-S^' o I , ltS)))
                (f (Fin-S^' (S m) (Fin-S^' o <I'))))
      == Cident n (Z (Fin-S^' m (ℕ-S^' o I , ltS)))
    sum-C-fwproj-fwin-late' m o {I = O} Z f = idp
    sum-C-fwproj-fwin-late' m o {I = S I} Z f =
      ap2 (Group.comp (C n (Z (Fin-S^' m (ℕ-S^' (S o) I , ltS)))))
        (sum-C-fwproj-fwin-late' m (S o) Z f)
        (C-fwproj-fwin-late m Z _ _)
      ∙ Group.unit-l (C n (Z (Fin-S^' m (ℕ-S^' (S o) I , ltS)))) _

    sum-C-fwproj-fwin-late : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) (f : Π _ (CEl n ∘ Z))
      →  Group.sum (C n (Z (Fin-S^' m (I , ltS))))
           (λ <I' → CEl-fmap n
                (⊙fwproj (Fin-S^' (S m) <I') ⊙∘ ⊙fwin {X = Z} (Fin-S^' m (I , ltS)))
                (f (Fin-S^' (S m) <I')))
      == Cident n (Z (Fin-S^' m (I , ltS)))
    sum-C-fwproj-fwin-late m = sum-C-fwproj-fwin-late' m O
  
    sum-C-fwproj-fwin' : ∀ m {I} (Z : Fin (ℕ-S^' m I) → Ptd₀) (f : Π _ (CEl n ∘ Z)) (<I : Fin I)
      → Group.sum (C n (Z (Fin-S^' m <I)))
          (λ <I' → CEl-fmap n
            (⊙fwproj (Fin-S^' m <I') ⊙∘ ⊙fwin {X = Z} (Fin-S^' m <I))
            (f (Fin-S^' m <I')))
      == f (Fin-S^' m <I)
    sum-C-fwproj-fwin' m Z f (I , ltS) =
      ap2 (Group.comp (C n (Z (Fin-S^' m (I , ltS)))))
        (sum-C-fwproj-fwin-late m Z f)
        (C-fwproj-fwin-diag Z (Fin-S^' m (I , ltS)) (f (Fin-S^' m (I , ltS))))
      ∙ Group.unit-l (C n (Z (Fin-S^' m (I , ltS)))) _
    sum-C-fwproj-fwin' m {I = S I} Z f (o , ltSR o<I) =
      ap2 (Group.comp (C n (Z (Fin-S^' (S m) (o , o<I)))))
        (sum-C-fwproj-fwin' (S m) Z f (o , o<I))
        (C-fwproj-fwin-early m Z (o , o<I) (f (Fin-S^' m (I , ltS))))
      ∙ Group.unit-r (C n (Z (Fin-S^' (S m) (o , o<I)))) _
      
    sum-C-fwproj-fwin : ∀ {I} (Z : Fin I → Ptd₀) (f : Π (Fin I) (CEl n ∘ Z)) (<I : Fin I)
      →  Group.sum (C n (Z <I)) (λ <I' → CEl-fmap n (⊙fwproj <I' ⊙∘ ⊙fwin {X = Z} <I) (f <I'))
      == f <I
    sum-C-fwproj-fwin = sum-C-fwproj-fwin' O

    inverse-C-finite-additive-is-inverse' : ∀ {I} (Z : Fin I → Ptd₀)
      → ∀ f → GroupHom.f (C-additive-hom n Z) (inverse-C-finite-additive Z f) ∼ f
    inverse-C-finite-additive-is-inverse' Z f <I =
      CEl-fmap n (⊙fwin {X = Z} <I) (Group.sum (C n (⊙FinWedge Z)) (λ <I → CEl-fmap n (⊙fwproj <I) (f <I)))
        =⟨ GroupHom.pres-sum (C-fmap n (⊙fwin {X = Z} <I)) (λ <I → CEl-fmap n (⊙fwproj <I) (f <I)) ⟩
      Group.sum (C n (Z <I)) (λ <I' → CEl-fmap n (⊙fwin {X = Z} <I) (CEl-fmap n (⊙fwproj <I') (f <I')))
        =⟨ ap (Group.sum (C n (Z <I))) (λ= λ <I' → ∘-CEl-fmap n (⊙fwin {X = Z} <I) (⊙fwproj <I') (f <I')) ⟩
      Group.sum (C n (Z <I)) (λ <I' → CEl-fmap n (⊙fwproj <I' ⊙∘ ⊙fwin {X = Z} <I) (f <I'))
        =⟨ sum-C-fwproj-fwin Z f <I ⟩
      f <I
        =∎
    
  inverse-C-finite-additive-matches : ∀ {I} (Z : Fin I → Ptd₀)
    → is-equiv.g (C-finite-additive Z) ∼ inverse-C-finite-additive Z
  inverse-C-finite-additive-matches {I} Z f =
    ! $ equiv-adj (GroupIso.f-equiv (C-finite-additive-iso Z)) $
      λ= $ inverse-C-finite-additive-is-inverse' Z f

  private
    C-fwproj-basis-late : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) <I g
      → CEl-fmap n (⊙fwproj (Fin-S^' (S m) <I))
          (Πᴳ-basis (C n ∘ Z) (Fin-S^' m (I , ltS)) g (Fin-S^' (S m) <I))
      == Cident n (⊙FinWedge Z)
    C-fwproj-basis-late m Z <I g =
      ap (CEl-fmap n (⊙fwproj (Fin-S^' (S m) <I)))
         (Πᴳ-basis-early m (C n ∘ Z) <I g)
      ∙ GroupHom.pres-ident (C-fmap n (⊙fwproj (Fin-S^' (S m) <I)))

    C-fwproj-basis-early : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) <I g
      → CEl-fmap n (⊙fwproj (Fin-S^' m (I , ltS)))
          (Πᴳ-basis (C n ∘ Z) (Fin-S^' (S m) <I) g (Fin-S^' m (I , ltS)))
      == Cident n (⊙FinWedge Z)
    C-fwproj-basis-early m {I} Z <I g =
      ap (CEl-fmap n (⊙fwproj (Fin-S^' m (I , ltS))))
         (Πᴳ-basis-late m (C n ∘ Z) <I g)
      ∙ GroupHom.pres-ident (C-fmap n (⊙fwproj (Fin-S^' m (I , ltS))))

    C-fwproj-basis-diag : ∀ {I} (Z : Fin I → Ptd₀) <I g
      → CEl-fmap n (⊙fwproj <I) (Πᴳ-basis (C n ∘ Z) <I g <I)
      == CEl-fmap n (⊙fwproj {X = Z} <I) g
    C-fwproj-basis-diag Z <I g =
      ap (CEl-fmap n (⊙fwproj <I)) (Πᴳ-basis-diag (C n ∘ Z) <I g)

    sum-C-fwproj-basis-late' : ∀ m o {I} (Z : Fin (ℕ-S^' (S m) (ℕ-S^' o I)) → Ptd₀) g
      → Group.sum (C n (⊙FinWedge Z))
          (λ <I' → CEl-fmap n (⊙fwproj (Fin-S^' (S m) (Fin-S^' o <I')))
            (Πᴳ-basis (C n ∘ Z) (Fin-S^' m (ℕ-S^' o I , ltS)) g (Fin-S^' (S m) (Fin-S^' o <I'))))
      == Cident n (⊙FinWedge Z)
    sum-C-fwproj-basis-late' m o {I = O} Z g = idp
    sum-C-fwproj-basis-late' m o {I = S I} Z g =
      ap2 (Group.comp (C n (⊙FinWedge Z)))
        (sum-C-fwproj-basis-late' m (S o) Z g)
        (C-fwproj-basis-late m Z (Fin-S^' o (I , ltS)) g)
      ∙ Group.unit-l (C n (⊙FinWedge Z)) _

    sum-C-fwproj-basis-late : ∀ m {I} (Z : Fin (ℕ-S^' (S m) I) → Ptd₀) g
      → Group.sum (C n (⊙FinWedge Z))
          (λ <I' → CEl-fmap n (⊙fwproj (Fin-S^' (S m) <I'))
            (Πᴳ-basis (C n ∘ Z) (Fin-S^' m (I , ltS)) g (Fin-S^' (S m) <I')))
      == Cident n (⊙FinWedge Z)
    sum-C-fwproj-basis-late m = sum-C-fwproj-basis-late' m O

    sum-C-fwproj-basis' : ∀ m {I} (Z : Fin (ℕ-S^' m I) → Ptd₀) <I g
      → Group.sum (C n (⊙FinWedge Z))
          (λ <I' → CEl-fmap n (⊙fwproj (Fin-S^' m <I')) (Πᴳ-basis (C n ∘ Z) (Fin-S^' m <I) g (Fin-S^' m <I')))
      == CEl-fmap n (⊙fwproj {X = Z} (Fin-S^' m <I)) g
    sum-C-fwproj-basis' m Z (I , ltS) g =
      ap2 (Group.comp (C n (⊙FinWedge Z)))
        (sum-C-fwproj-basis-late m Z g)
        (C-fwproj-basis-diag Z (Fin-S^' m (I , ltS)) g)
      ∙ Group.unit-l (C n (⊙FinWedge Z)) _
    sum-C-fwproj-basis' m Z (o , ltSR o<I) g =
      ap2 (Group.comp (C n (⊙FinWedge Z)))
        (sum-C-fwproj-basis' (S m) Z (o , o<I) g)
        (C-fwproj-basis-early m Z (o , o<I) g)
      ∙ Group.unit-r (C n (⊙FinWedge Z)) _

  inverse-C-finite-additive-basis : ∀ {I} (Z : Fin I → Ptd₀) <I g
    →  inverse-C-finite-additive Z (Πᴳ-basis (C n ∘ Z) <I g)
    == CEl-fmap n (⊙fwproj {X = Z} <I) g
  inverse-C-finite-additive-basis = sum-C-fwproj-basis' O

  inverse-C-finite-additive-basis' : ∀ {I} (Z : Fin I → Ptd₀) <I g
    → is-equiv.g (C-finite-additive Z) (Πᴳ-basis (C n ∘ Z) <I g)
    == CEl-fmap n (⊙fwproj {X = Z} <I) g
  inverse-C-finite-additive-basis' Z <I g =
      inverse-C-finite-additive-matches Z (Πᴳ-basis (C n ∘ Z) <I g)
    ∙ inverse-C-finite-additive-basis Z <I g
