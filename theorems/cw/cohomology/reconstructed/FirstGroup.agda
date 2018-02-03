{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import cohomology.PtdMapSequence
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence
open import groups.KernelImageUniqueFactorization

open import cw.CW

module cw.cohomology.reconstructed.FirstGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 2) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cohomology.LongExactSequence cohomology-theory
open import cw.cohomology.WedgeOfCells OT
open import cw.cohomology.grid.PtdMap (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
open import cw.cohomology.reconstructed.TipAndAugment OT (⊙cw-take (lteSR lteS) ⊙skel)
open import cw.cohomology.reconstructed.TipCoboundary OT (⊙cw-init ⊙skel)
open import cw.cohomology.reconstructed.HigherCoboundary OT ⊙skel
open import cw.cohomology.reconstructed.HigherCoboundaryGrid OT ⊙skel ac
open import cw.cohomology.reconstructed.TipGrid OT (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)
open import cw.cohomology.reconstructed.TopGrid OT 1 (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)

private
  0≤2 : 0 ≤ 2
  0≤2 = lteSR lteS

  ac₀ = ⊙take-has-cells-with-choice 0≤2 ⊙skel ac

{-
              H
    Coker ≃ C(X₁)<------C(X₂) = C(X)
              ^           ^
              |           |
              |           |
           C(X₁/X₀)<---C(X₂/X₀) ≃ Ker
             WoC          G

    WoC := Wedges of Cells
-}

private
  G : Group i
  G = C 1 (⊙Cofiber (⊙cw-incl-tail 0≤2 ⊙skel))

  G-iso-Ker : G ≃ᴳ Ker.grp cw-co∂-last
  G-iso-Ker = Ker-cw-co∂-last

  H : Group i
  H = C 1 ⊙⟦ ⊙cw-init ⊙skel ⟧

  Coker-iso-H : CokerCo∂Head.grp ≃ᴳ H
  Coker-iso-H = Coker-cw-co∂-head

  G-to-C-cw : G →ᴳ C 1 ⊙⟦ ⊙skel ⟧
  G-to-C-cw = C-fmap 1 (⊙cfcod' (⊙cw-incl-tail 0≤2 ⊙skel))

  abstract
    G-to-C-cw-is-surj : is-surjᴳ G-to-C-cw
    G-to-C-cw-is-surj = Exact.K-trivial-implies-φ-is-surj
      (exact-seq-index 2 $ C-cofiber-exact-seq 0 (⊙cw-incl-tail 0≤2 ⊙skel))
      (CX₀-≠-is-trivial (pos-≠ (ℕ-S≠O 0)) ac₀)

  C-cw-to-H : C 1 ⊙⟦ ⊙skel ⟧ →ᴳ H
  C-cw-to-H = C-fmap 1 (⊙cw-incl-last ⊙skel)

  abstract
    C-cw-to-H-is-inj : is-injᴳ C-cw-to-H
    C-cw-to-H-is-inj = Exact.G-trivial-implies-ψ-is-inj
      (exact-seq-index 2 $ C-cofiber-exact-seq 0 (⊙cw-incl-last ⊙skel))
      (CXₙ/Xₙ₋₁-<-is-trivial ⊙skel ltS ac)

  C-WoC : Group i
  C-WoC = C 1 (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))

  G-to-C-WoC : G →ᴳ C-WoC
  G-to-C-WoC = C-fmap 1 Y/X-to-Z/X

  C-WoC-to-H : C-WoC →ᴳ H
  C-WoC-to-H = C-fmap 1 (⊙cfcod' (⊙cw-incl-last (⊙cw-init ⊙skel)))

open import groups.KernelImage cw-co∂-last cw-co∂-head CX₁/X₀-is-abelian

C-cw-iso-ker/im : C 1 ⊙⟦ ⊙skel ⟧ ≃ᴳ Ker/Im
C-cw-iso-ker/im = H-iso-Ker/Im
  cw-co∂-last cw-co∂-head CX₁/X₀-is-abelian
  φ₁ φ₁-is-surj φ₂ φ₂-is-inj lemma-comm
  where
    φ₁ = G-to-C-cw ∘ᴳ GroupIso.g-hom G-iso-Ker
    abstract
      φ₁-is-surj : is-surjᴳ φ₁
      φ₁-is-surj = ∘-is-surj G-to-C-cw-is-surj (equiv-is-surj (GroupIso.g-is-equiv G-iso-Ker))

    φ₂ = GroupIso.g-hom Coker-iso-H ∘ᴳ C-cw-to-H
    abstract
      φ₂-is-inj : is-injᴳ φ₂
      φ₂-is-inj = ∘-is-inj (equiv-is-inj (GroupIso.g-is-equiv Coker-iso-H)) C-cw-to-H-is-inj

    abstract
      lemma-comm : ∀ g →
           GroupIso.g Coker-iso-H (GroupHom.f (C-cw-to-H ∘ᴳ G-to-C-cw) (GroupIso.g G-iso-Ker g))
        == q[ fst g ]
      lemma-comm g =
        GroupIso.g Coker-iso-H (GroupHom.f C-cw-to-H (GroupHom.f G-to-C-cw (GroupIso.g G-iso-Ker g)))
          =⟨ ap (GroupIso.g Coker-iso-H) (! (C-top-grid-commutes □$ᴳ GroupIso.g G-iso-Ker g)) ⟩
        GroupIso.g Coker-iso-H (GroupHom.f C-WoC-to-H (GroupHom.f G-to-C-WoC (GroupIso.g G-iso-Ker g)))
          =⟨ ap (GroupIso.g Coker-iso-H ∘ GroupHom.f C-WoC-to-H ∘ fst) (GroupIso.f-g G-iso-Ker g) ⟩
        GroupIso.g Coker-iso-H (GroupHom.f C-WoC-to-H (fst g))
          =⟨ GroupIso.g-f Coker-iso-H q[ fst g ] ⟩
        q[ fst g ]
          =∎
