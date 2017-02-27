{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence
open import groups.PropQuotUniqueFactorization
import cw.cohomology.GridPtdMap as GPM

open import cw.CW

module cw.cohomology.HigherCohomologyGroups {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S (S (S n)))) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cohomology.LongExactSequence cohomology-theory
  (ℕ-to-ℤ (S n)) (⊙cw-incl-tail (inr (ltSR (ltSR ltS))) ⊙skel)
open import cw.cohomology.CoboundaryGrid OT
open import cw.cohomology.Descending OT
open import cw.cohomology.InnerGrid OT (ℕ-to-ℤ (S (S n)))
  (⊙cw-incl-last (⊙cw-init (⊙cw-init ⊙skel)))
  (⊙cw-incl-last (⊙cw-init ⊙skel))
  (⊙cw-incl-last ⊙skel)
open import cw.cohomology.WedgeOfCells OT
import cw.cohomology.GridLongExactSequence cohomology-theory as GLES

private
  Sn≤SSSn : S n ≤ S (S (S n))
  Sn≤SSSn = inr (ltSR ltS)

  n≤SSn : n ≤ S (S n)
  n≤SSn = inr (ltSR ltS)

  n≤SSSn : n ≤ S (S (S n))
  n≤SSSn = inr (ltSR (ltSR ltS))

  ⊙skel₋₃ = ⊙cw-take n≤SSSn ⊙skel
  ac₋₃ = ⊙take-has-cells-with-choice n≤SSSn ⊙skel ac

{-
              H          apex
   Coker ≃ C(X₂/X₀)<---C(X₃/X₀) ≃ C(X)
              ^           ^
              |           |
              |           |
           C(X₂/X₁)<---C(X₃/X₁) ≃ Ker
             WoC          G

    WoC := Wedges of Cells
-}

private
  C-apex : Group i
  C-apex = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSSn ⊙skel))

  C-apex-iso-C-cw : C-apex ≃ᴳ C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧
  C-apex-iso-C-cw = Exact2.G-trivial-and-L-trivial-implies-H-iso-K
    (exact-seq-index 1 C-cofiber-exact-seq)
    (exact-seq-index 2 C-cofiber-exact-seq)
    (C-cw-at-higher (S n) ltS ⊙skel₋₃ ac₋₃)
    (C-cw-at-higher (S (S n)) (ltSR ltS) ⊙skel₋₃ ac₋₃)

  G : Group i
  G = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail Sn≤SSSn ⊙skel))

  G-iso-Ker : G ≃ᴳ Ker.grp (cw-co∂-last ⊙skel ac)
  G-iso-Ker = Ker-cw-co∂-last ⊙skel ac

  H : Group i
  H = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-tail n≤SSn (⊙cw-init ⊙skel)))

  Coker-iso-H : CokerCo∂.grp (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac) ≃ᴳ H
  Coker-iso-H = Coker-cw-co∂-last (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)

  module GLES-top = GLES (ℕ-to-ℤ (S n))
    (⊙cw-incl-nth Sn≤SSSn ⊙skel) (⊙cw-incl-tail Sn≤SSSn ⊙skel)
  module GPM-top = GPM
    (⊙cw-incl-nth Sn≤SSSn ⊙skel) (⊙cw-incl-tail Sn≤SSSn ⊙skel)

  G-to-C-apex : G →ᴳ C-apex
  G-to-C-apex = C-fmap (ℕ-to-ℤ (S (S n))) GPM-top.Z/X-to-Z/Y

  abstract
    G-to-C-apex-is-surj : is-surjᴳ G-to-C-apex
    G-to-C-apex-is-surj = Exact.K-trivial-implies-φ-is-surj
      (exact-seq-index 2 GLES-top.C-grid-cofiber-exact-seq)
      (C-Cofiber-cw-incl-last->-is-trivial (S (S n)) ltS (⊙cw-take Sn≤SSSn ⊙skel)
        (⊙take-has-cells-with-choice Sn≤SSSn ⊙skel ac))

  module GLES-right = GLES (ℕ-to-ℤ (S n))
    (⊙cw-incl-tail n≤SSn (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
  module GPM-right = GPM
    (⊙cw-incl-tail n≤SSn (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

  C-apex-to-H : C-apex →ᴳ H
  C-apex-to-H = C-fmap (ℕ-to-ℤ (S (S n))) GPM-right.Y/X-to-Z/X

  abstract
    C-apex-to-H-is-inj : is-injᴳ C-apex-to-H
    C-apex-to-H-is-inj = Exact.G-trivial-implies-ψ-is-inj
      (exact-seq-index 2 GLES-right.C-grid-cofiber-exact-seq)
      (C-Cofiber-cw-incl-last-<-is-trivial (S (S n)) ltS ⊙skel ac)

  C-WoC : Group i
  C-WoC = C (ℕ-to-ℤ (S (S n))) (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))

  G-to-C-WoC : G →ᴳ C-WoC
  G-to-C-WoC = C-fmap (ℕ-to-ℤ (S (S n)))
    (GPM.Y/X-to-Z/X (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel))

  C-WoC-to-H : C-WoC →ᴳ H
  C-WoC-to-H = C-fmap (ℕ-to-ℤ (S (S n)))
    (GPM.Z/X-to-Z/Y (⊙cw-incl-nth Sn≤SSSn ⊙skel) (⊙cw-incl-last (⊙cw-init ⊙skel)))

C-cw-iso-ker/im :
     C (ℕ-to-ℤ (S (S n))) ⊙⟦ ⊙skel ⟧
  ≃ᴳ QuotGroup (quot-of-sub
      (ker-propᴳ (cw-co∂-last ⊙skel ac))
      (CokerCo∂.npropᴳ (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)))
C-cw-iso-ker/im = lemma ∘eᴳ C-apex-iso-C-cw ⁻¹ᴳ where
  abstract
    lemma-comm : ∀ g →
         GroupIso.g Coker-iso-H (GroupHom.f (C-apex-to-H ∘ᴳ G-to-C-apex) (GroupIso.g G-iso-Ker g))
      == q[ fst g ]
    lemma-comm g =
      GroupIso.g Coker-iso-H (GroupHom.f C-apex-to-H (GroupHom.f G-to-C-apex (GroupIso.g G-iso-Ker g)))
        =⟨ ap (GroupIso.g Coker-iso-H) (! (C-inner-grid-commutes □$ᴳ GroupIso.g G-iso-Ker g)) ⟩
      GroupIso.g Coker-iso-H (GroupHom.f C-WoC-to-H (GroupHom.f G-to-C-WoC (GroupIso.g G-iso-Ker g)))
        =⟨ ap (GroupIso.g Coker-iso-H ∘ GroupHom.f C-WoC-to-H ∘ fst) (GroupIso.f-g G-iso-Ker g) ⟩
      GroupIso.g Coker-iso-H (GroupHom.f C-WoC-to-H (fst g))
        =⟨ GroupIso.g-f Coker-iso-H q[ fst g ] ⟩
      q[ fst g ]
        =∎

  lemma : C-apex
       ≃ᴳ QuotGroup (quot-of-sub
            (ker-propᴳ (cw-co∂-last ⊙skel ac))
            (CokerCo∂.npropᴳ (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)))
  lemma = H-iso-P/Q
    (ker-propᴳ (cw-co∂-last ⊙skel ac))
    (CokerCo∂.npropᴳ (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac))
    (G-to-C-apex ∘ᴳ GroupIso.g-hom G-iso-Ker)
    (∘-is-surj G-to-C-apex-is-surj (equiv-is-surj (GroupIso.g-is-equiv G-iso-Ker)))
    (GroupIso.g-hom Coker-iso-H  ∘ᴳ C-apex-to-H)
    (∘-is-inj (equiv-is-inj (GroupIso.g-is-equiv Coker-iso-H)) C-apex-to-H-is-inj)
    lemma-comm
