{-# OPTIONS --without-K --rewriting #-}

open import HoTT

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
