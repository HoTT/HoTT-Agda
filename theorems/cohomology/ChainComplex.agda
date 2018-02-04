{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.KernelImage
open import groups.KernelImageEmap

module cohomology.ChainComplex where

  record ChainComplex i : Type (lsucc i) where
    field
      head : AbGroup i
      chain : ℕ → AbGroup i
      augment : AbGroup.grp (chain 0) →ᴳ AbGroup.grp head
      boundary : ∀ n → (AbGroup.grp (chain (S n)) →ᴳ AbGroup.grp (chain n))

  record CochainComplex i : Type (lsucc i) where
    field
      head : AbGroup i
      cochain : ℕ → AbGroup i
      augment : AbGroup.grp head →ᴳ AbGroup.grp (cochain 0)
      coboundary : ∀ n → (AbGroup.grp (cochain n) →ᴳ AbGroup.grp (cochain (S n)))

  record CochainComplexEquiv {i₀ i₁}
    (cc₀ : CochainComplex i₀) (cc₁ : CochainComplex i₁) : Type (lmax i₀ i₁) where
    private
      module cc₀ = CochainComplex cc₀
      module cc₁ = CochainComplex cc₁
    field
      head : AbGroup.grp cc₀.head ≃ᴳ AbGroup.grp cc₁.head
      cochain : (n : ℕ) → AbGroup.grp (cc₀.cochain n) ≃ᴳ AbGroup.grp (cc₁.cochain n)
      augment : CommSquareᴳ cc₀.augment cc₁.augment (–>ᴳ head) (–>ᴳ (cochain 0))
      coboundary : ∀ n → CommSquareᴳ (cc₀.coboundary n) (cc₁.coboundary n)
        (–>ᴳ (cochain n)) (–>ᴳ (cochain (S n)))

  homology-group : ∀ {i} → ChainComplex i → (n : ℤ) → Group i
  homology-group cc (pos 0) = Ker/Im cc.augment (cc.boundary 0) (snd (cc.chain 0))
    where module cc = ChainComplex cc
  homology-group cc (pos (S n)) = Ker/Im (cc.boundary n) (cc.boundary (S n)) (snd (cc.chain (S n)))
    where module cc = ChainComplex cc
  homology-group {i} cc (negsucc _) = Lift-group {j = i} Unit-group

  cohomology-group : ∀ {i} → CochainComplex i → (n : ℤ) → Group i
  cohomology-group cc (pos 0) = Ker/Im (cc.coboundary 0) cc.augment (snd (cc.cochain 0))
    where module cc = CochainComplex cc
  cohomology-group cc (pos (S n)) = Ker/Im (cc.coboundary (S n)) (cc.coboundary n) (snd (cc.cochain (S n)))
    where module cc = CochainComplex cc
  cohomology-group {i} cc (negsucc _) = Lift-group {j = i} Unit-group

  cohomology-group-emap : ∀ {i₀ i₁} {cc₀ : CochainComplex i₀} {cc₁ : CochainComplex i₁}
    → CochainComplexEquiv cc₀ cc₁
    → (n : ℤ) → cohomology-group cc₀ n ≃ᴳ cohomology-group cc₁ n
  cohomology-group-emap {cc₀ = cc₀} {cc₁} cc= (pos 0) =
    Ker/Im-emap (snd (cc₀.cochain 0)) (snd (cc₁.cochain 0))
      (cc=.coboundary 0) cc=.augment
      (snd cc=.head) (snd (cc=.cochain 0)) (snd (cc=.cochain 1))
    where module cc₀ = CochainComplex cc₀
          module cc₁ = CochainComplex cc₁
          module cc= = CochainComplexEquiv cc=
  cohomology-group-emap {cc₀ = cc₀} {cc₁} cc= (pos (S n)) =
    Ker/Im-emap (snd (cc₀.cochain (S n))) (snd (cc₁.cochain (S n)))
      (cc=.coboundary (S n)) (cc=.coboundary n)
      (snd (cc=.cochain n)) (snd (cc=.cochain (S n))) (snd (cc=.cochain (S (S n))))
    where module cc₀ = CochainComplex cc₀
          module cc₁ = CochainComplex cc₁
          module cc= = CochainComplexEquiv cc=
  cohomology-group-emap _ (negsucc _) = lift-iso ∘eᴳ lower-iso

  complex-dualize : ∀ {i j} → ChainComplex i → AbGroup j
    →  CochainComplex (lmax i j)
  complex-dualize {i} {j} cc G = record {M} where
    module cc = ChainComplex cc
    module M where
      head : AbGroup (lmax i j)
      head = hom-abgroup (AbGroup.grp cc.head) G

      cochain : ℕ → AbGroup (lmax i j)
      cochain n = hom-abgroup (AbGroup.grp (cc.chain n)) G

      augment : AbGroup.grp head →ᴳ AbGroup.grp (cochain 0)
      augment = pre∘ᴳ-hom G cc.augment

      coboundary : ∀ n → (AbGroup.grp (cochain n) →ᴳ AbGroup.grp (cochain (S n)))
      coboundary n = pre∘ᴳ-hom G (cc.boundary n)
