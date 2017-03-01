{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.KernelImage

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

  homology-group : ∀ {i} → ChainComplex i
    → (n : ℕ) → Group i
  homology-group cc 0 = Ker/Im cc.augment (cc.boundary 0) (snd (cc.chain 0))
    where module cc = ChainComplex cc
  homology-group cc (S n) = Ker/Im (cc.boundary n) (cc.boundary (S n)) (snd (cc.chain (S n)))
    where module cc = ChainComplex cc

  cohomology-group : ∀ {i} → CochainComplex i
    → (n : ℕ) → Group i
  cohomology-group cc 0 = Ker/Im (cc.coboundary 0) cc.augment (snd (cc.cochain 0))
    where module cc = CochainComplex cc
  cohomology-group cc (S n) = Ker/Im (cc.coboundary (S n)) (cc.coboundary n) (snd (cc.cochain (S n)))
    where module cc = CochainComplex cc

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
