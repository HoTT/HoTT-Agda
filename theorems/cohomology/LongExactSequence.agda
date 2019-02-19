{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import groups.ExactSequence
open import groups.HomSequence
open import homotopy.CofiberSequence

module cohomology.LongExactSequence {i} (CT : CohomologyTheory i)
  {X Y : Ptd i} (n : ℤ) (f : X ⊙→ Y) where

open CohomologyTheory CT
open import cohomology.PtdMapSequence CT

co∂ : C n X →ᴳ C (succ n) (⊙Cofiber f)
co∂ = record {f = CEl-fmap (succ n) ⊙extract-glue ∘ GroupIso.g (C-Susp n X); pres-comp = lemma} where
  abstract lemma = ∘ᴳ-pres-comp (C-fmap (succ n) ⊙extract-glue) (GroupIso.g-hom (C-Susp n X))

⊙∂-before-Susp : ⊙Cofiber f ⊙→ ⊙Susp (de⊙ X)
⊙∂-before-Susp = ⊙extract-glue

∂-before-Susp : Cofiber (fst f) → Susp (de⊙ X)
∂-before-Susp = extract-glue

abstract
  ∂-before-Susp-glue-β : ∀ x →
    ap ∂-before-Susp (cfglue x) == merid x
  ∂-before-Susp-glue-β = ExtractGlue.glue-β

C-cofiber-seq : HomSequence (C n Y) (C (succ n) X)
C-cofiber-seq =
  C n Y                   →⟨ C-fmap n f                  ⟩ᴳ
  C n X                   →⟨ co∂                         ⟩ᴳ
  C (succ n) (⊙Cofiber f) →⟨ C-fmap (succ n) (⊙cfcod' f) ⟩ᴳ
  C (succ n) Y            →⟨ C-fmap (succ n) f           ⟩ᴳ
  C (succ n) X            ⊣|ᴳ

private
  C-iterated-cofiber-seq = C-seq (succ n) (iterated-cofiber-seq f)

  C-iterated-cofiber-seq-is-exact : is-exact-seq C-iterated-cofiber-seq
  C-iterated-cofiber-seq-is-exact =
    C-exact (succ n) (⊙cfcod²' f) , C-exact (succ n) (⊙cfcod' f) , C-exact (succ n) f , lift tt

  -- An intermediate sequence for proving exactness of [C-cofiber-seq].
  C-cofiber-seq' = C-seq (succ n) (cyclic-cofiber-seq f)

  C-cofiber-seq'-is-exact : is-exact-seq C-cofiber-seq'
  C-cofiber-seq'-is-exact =
    seq-equiv-preserves'-exact
      (C-seq-emap (succ n) (iterated-equiv-cyclic f))
      C-iterated-cofiber-seq-is-exact

  -- Now the final sequence
  C-cofiber-seq'-to-C-cofiber-seq :
    HomSeqMap C-cofiber-seq' C-cofiber-seq
      (GroupIso.f-hom (C-Susp n Y)) (idhom _)
  C-cofiber-seq'-to-C-cofiber-seq =
    GroupIso.f-hom (C-Susp n Y) ↓⟨ C-Susp-fmap n f ⟩ᴳ
    GroupIso.f-hom (C-Susp n X) ↓⟨ comm-sqrᴳ (λ x → ap (CEl-fmap (succ n) ⊙extract-glue) (! $ GroupIso.g-f (C-Susp n X) x)) ⟩ᴳ
    idhom _                     ↓⟨ comm-sqrᴳ (λ _ → idp) ⟩ᴳ
    idhom _                     ↓⟨ comm-sqrᴳ (λ _ → idp) ⟩ᴳ
    idhom _                     ↓|ᴳ

  C-cofiber-seq'-equiv-C-cofiber-seq :
    HomSeqEquiv C-cofiber-seq' C-cofiber-seq
      (GroupIso.f-hom (C-Susp n Y)) (idhom _)
  C-cofiber-seq'-equiv-C-cofiber-seq =
    C-cofiber-seq'-to-C-cofiber-seq ,
    (GroupIso.f-is-equiv (C-Susp n Y) , GroupIso.f-is-equiv (C-Susp n X) , idf-is-equiv _ , idf-is-equiv _ , idf-is-equiv _)

abstract
  C-cofiber-seq-is-exact : is-exact-seq C-cofiber-seq
  C-cofiber-seq-is-exact = seq-equiv-preserves-exact
    C-cofiber-seq'-equiv-C-cofiber-seq C-cofiber-seq'-is-exact

C-cofiber-exact-seq : ExactSequence (C n Y) (C (succ n) X)
C-cofiber-exact-seq = C-cofiber-seq , C-cofiber-seq-is-exact
