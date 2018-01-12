{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.ExactSequence
open import groups.HomSequence

module cw.cohomology.GridLongExactSequence {i} (CT : CohomologyTheory i)
  {X Y Z : Ptd i} (n : ℤ) (f : X ⊙→ Y) (g : Y ⊙→ Z) where

open CohomologyTheory CT
open import cohomology.PtdMapSequence CT
open import cw.cohomology.CofiberGrid (fst f) (fst g)
open import cw.cohomology.GridPtdMap f g

{-
  X --> Y ----> Z
        |       |
        v       v
       Y/X --> Z/X
        | this  |
        v   one v
        1 ---> Z/Y
-}

private
  ⊙D-span : ⊙Span
  ⊙D-span = ⊙span Y/X Z Y (⊙cfcod' f) g

  ⊙D : Ptd i
  ⊙D = ⊙Pushout ⊙D-span

  Y/X-to-D : Y/X ⊙→ ⊙D
  Y/X-to-D = B/A-to-D , idp

  open import cohomology.LongExactSequence CT n Y/X-to-D

  ⊙E : Ptd i
  ⊙E = ⊙Cofiber (⊙left ⊙D-span)

  Z/Y-to-E : Z/Y ⊙→ ⊙E
  Z/Y-to-E = C/B-to-E , idp

  Z/X-to-D : Z/X ⊙→ ⊙D
  Z/X-to-D = C/A-to-D , idp

grid-co∂ : C n Y/X →ᴳ C (succ n) Z/Y
grid-co∂ = record {f = CEl-fmap (succ n) Z/Y-to-E ∘ GroupHom.f co∂ ; pres-comp = lemma} where
  abstract lemma = ∘ᴳ-pres-comp (C-fmap (succ n) Z/Y-to-E) co∂

C-grid-cofiber-seq : HomSequence (C n Z/X) (C (succ n) Y/X)
C-grid-cofiber-seq =
  C n Z/X         →⟨ C-fmap n Y/X-to-Z/X        ⟩ᴳ
  C n Y/X         →⟨ grid-co∂                   ⟩ᴳ
  C (succ n) Z/Y  →⟨ C-fmap (succ n) Z/X-to-Z/Y ⟩ᴳ
  C (succ n) Z/X  →⟨ C-fmap (succ n) Y/X-to-Z/X ⟩ᴳ
  C (succ n) Y/X  ⊣|ᴳ

private
  C-cofiber-seq-to-C-grid-cofiber-seq :
    HomSeqMap C-cofiber-seq C-grid-cofiber-seq
      (C-fmap n Z/X-to-D) (idhom _)
  C-cofiber-seq-to-C-grid-cofiber-seq =
    C-fmap n Z/X-to-D         ↓⟨ comm-sqrᴳ (λ d → ! (C-fmap-idf n _)
                                                ∙ (C-comm-square n B/A-to-C/A-comm-square □$ᴳ d)) ⟩ᴳ
    idhom _                   ↓⟨ comm-sqrᴳ (λ _ → idp) ⟩ᴳ
    C-fmap (succ n) Z/Y-to-E  ↓⟨ C-comm-square (succ n) C/A-to-C/B-comm-square ⟩ᴳ
    C-fmap (succ n) Z/X-to-D  ↓⟨ comm-sqrᴳ (λ d → ! (C-fmap-idf (succ n) _)
                                                ∙ (C-comm-square (succ n) B/A-to-C/A-comm-square □$ᴳ d)) ⟩ᴳ
    idhom _                   ↓|ᴳ

  C-cofiber-seq-equiv-C-grid-cofiber-seq :
    HomSeqEquiv C-cofiber-seq C-grid-cofiber-seq
      (C-fmap n Z/X-to-D) (idhom _)
  C-cofiber-seq-equiv-C-grid-cofiber-seq =
    C-cofiber-seq-to-C-grid-cofiber-seq ,
      CEl-isemap n Z/X-to-D C/A-to-D-is-equiv ,
      idf-is-equiv _ ,
      CEl-isemap (succ n) Z/Y-to-E C/B-to-E-is-equiv ,
      CEl-isemap (succ n) Z/X-to-D C/A-to-D-is-equiv ,
      idf-is-equiv _

abstract
  C-grid-cofiber-seq-is-exact : is-exact-seq C-grid-cofiber-seq
  C-grid-cofiber-seq-is-exact = seq-equiv-preserves-exact
    C-cofiber-seq-equiv-C-grid-cofiber-seq C-cofiber-seq-is-exact

C-grid-cofiber-exact-seq : ExactSequence (C n Z/X) (C (succ n) Y/X)
C-grid-cofiber-exact-seq = C-grid-cofiber-seq , C-grid-cofiber-seq-is-exact
