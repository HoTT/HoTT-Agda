{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory
open import cohomology.PtdMapSequence
open import groups.ExactSequence
open import groups.Exactness
open import groups.HomSequence
open import groups.PropQuotUniqueFactorization

open import cw.CW

module cw.cohomology.FirstCohomologyGroup {i} (OT : OrdinaryTheory i)
  (⊙skel : ⊙Skeleton {i} 2) (ac : ⊙has-cells-with-choice 0 ⊙skel i) where

open OrdinaryTheory OT
open import cohomology.LongExactSequence cohomology-theory 0 (⊙cw-incl-tail 0≤2 ⊙skel)
open import cw.cohomology.CoboundaryGrid OT ⊙skel ac
open import cw.cohomology.GridPtdMap (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
open import cw.cohomology.TipGrid OT (⊙cw-init ⊙skel) (fst ac)
open import cw.cohomology.TopGrid OT 1 (⊙cw-incl-last (⊙cw-init ⊙skel)) (⊙cw-incl-last ⊙skel)
open import cw.cohomology.WedgeOfCells OT

private
  0≤2 : 0 ≤ 2
  0≤2 = inr (ltSR ltS)

  ⊙skel₀ = ⊙cw-take 0≤2 ⊙skel
  ac₀ = fst (fst ac)

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
      (exact-seq-index 2 C-cofiber-exact-seq)
      (C-points-≠-is-trivial 1 (pos-≠ (ℕ-S≠O 0)) ⊙skel₀ ac₀)

  C-cw-to-H : C 1 ⊙⟦ ⊙skel ⟧ →ᴳ H
  C-cw-to-H = C-fmap 1 (⊙cw-incl-last ⊙skel)

  abstract
    C-cw-to-H-is-inj : is-injᴳ C-cw-to-H
    C-cw-to-H-is-inj = Exact.G-trivial-implies-ψ-is-inj
      (exact-seq-index 2 C-cofiber-exact-seq)
      (C-Cofiber-cw-incl-last-<-is-trivial 1 ltS ⊙skel ac)

  C-WoC : Group i
  C-WoC = C 1 (⊙Cofiber (⊙cw-incl-last (⊙cw-init ⊙skel)))

  G-to-C-WoC : G →ᴳ C-WoC
  G-to-C-WoC = C-fmap 1 Y/X-to-Z/X

  C-WoC-to-H : C-WoC →ᴳ H
  C-WoC-to-H = C-fmap 1 (⊙cfcod' (⊙cw-incl-last (⊙cw-init ⊙skel)))

C-cw-iso-ker/im :
  C 1 ⊙⟦ ⊙skel ⟧ ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-last) CokerCo∂Head.npropᴳ)
C-cw-iso-ker/im = lemma where
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

  lemma : C 1 ⊙⟦ ⊙skel ⟧
    ≃ᴳ QuotGroup (quot-of-sub (ker-propᴳ cw-co∂-last) CokerCo∂Head.npropᴳ)
  lemma = H-iso-P/Q
    (ker-propᴳ cw-co∂-last)
    CokerCo∂Head.npropᴳ
    (G-to-C-cw ∘ᴳ GroupIso.g-hom G-iso-Ker)
    (∘-is-surj G-to-C-cw-is-surj (equiv-is-surj (GroupIso.g-is-equiv G-iso-Ker)))
    (GroupIso.g-hom Coker-iso-H  ∘ᴳ C-cw-to-H)
    (∘-is-inj (equiv-is-inj (GroupIso.g-is-equiv Coker-iso-H)) C-cw-to-H-is-inj)
    lemma-comm
