{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CofiberSequence
open import groups.Exactness
open import groups.ExactSequence
open import groups.HomSequence
open import cohomology.Theory

module cohomology.Sigma {i} (CT : CohomologyTheory i)
  (n : ℤ) (X : Ptd i) (Y : de⊙ X → Ptd i) where

open CohomologyTheory CT
open import cohomology.Functor CT
open import cohomology.BaseIndependence CT
open import cohomology.PtdMapSequence CT

{- Cⁿ(Σx:X.Y) = Cⁿ(⋁x:X.Y) × Cⁿ(X). The proof is by constructing a
 - splitting exact sequence

       0 → Cⁿ(⋁x:X.Y) → Cⁿ(Σx:X.Y) → Cⁿ(X)

 - by observing that the map [select : x ↦ (x, pt Yₓ)] has a left inverse
 - and satisfies [Cofiber select == ⋁x:X.Y. -}


⊙select : X ⊙→ ⊙Σ X Y
⊙select = (bigwedge-f Y , idp)

⊙Σbwin : ⊙Σ X Y ⊙→ ⊙BigWedge Y
⊙Σbwin = ⊙cfcod' ⊙select

private
  seq : HomSequence _ _
  seq =
    C n (⊙Susp X)     →⟨ cst-hom ⟩ᴳ
    C n (⊙BigWedge Y) →⟨ C-fmap n ⊙Σbwin ⟩ᴳ
    C n (⊙Σ X Y)      →⟨ C-fmap n ⊙select ⟩ᴳ
    C n X             ⊣|ᴳ

  seq' : HomSequence _ _
  seq' =
    C n (⊙Susp X)     →⟨ C-fmap n ⊙extract-glue ⟩ᴳ
    C n (⊙BigWedge Y) →⟨ C-fmap n ⊙Σbwin ⟩ᴳ
    C n (⊙Σ X Y)      →⟨ C-fmap n ⊙select ⟩ᴳ
    C n X             ⊣|ᴳ

  seq'-to-seq : HomSeqMap seq' seq (idhom _) (idhom _)
  seq'-to-seq =
    idhom (C n (⊙Susp X))     ↓⟨ comm-sqrᴳ $ C-fmap-const n (extract-glue-from-BigWedge-is-const Y) ⟩ᴳ
    idhom (C n (⊙BigWedge Y)) ↓⟨ comm-sqrᴳ (λ _ → idp) ⟩ᴳ
    idhom (C n (⊙Σ X Y))      ↓⟨ comm-sqrᴳ (λ _ → idp) ⟩ᴳ
    idhom (C n X)             ↓|ᴳ

  seq'-equiv-seq : HomSeqEquiv seq' seq (idhom _) (idhom _)
  seq'-equiv-seq = seq'-to-seq ,
    idf-is-equiv _ , idf-is-equiv _ , idf-is-equiv _ , idf-is-equiv _

  abstract
    -- XXX This is not reusing cohomology.LongExactSequence.
    seq'-is-exact : is-exact-seq seq'
    seq'-is-exact = snd $ seq-equiv-preserves-exact
      (HomSeqEquiv-inverse (C-seq-emap n (cofiber-seq-equiv ⊙select)))
      (C-exact n (⊙cfcod' ⊙Σbwin) , C-exact n ⊙Σbwin , C-exact n ⊙select , lift tt)

    seq-is-exact : is-exact-seq seq
    seq-is-exact = seq-equiv-preserves-exact seq'-equiv-seq seq'-is-exact

  χ : C n X →ᴳ C n (⊙Σ X Y)
  χ = C-fmap n (⊙fstᵈ Y)

  abstract
    select-χ-is-idf : ∀ s → CEl-fmap n ⊙select (GroupHom.f χ s) == s
    select-χ-is-idf = CEl-fmap-inverse n ⊙select (⊙fstᵈ Y) λ _ → idp

iso : C n (⊙Σ X Y) ≃ᴳ C n (⊙BigWedge Y) ×ᴳ C n X
iso = Exact.φ-inj-and-ψ-has-rinv-split
  (exact-seq-index 1 (seq , seq-is-exact))
  (C-is-abelian n _)
  (Exact.φ-const-implies-ψ-is-inj
    (exact-seq-index 0 (seq , seq-is-exact))
    (λ _ → idp))
  χ select-χ-is-idf

{-
  ⊙Σbwin-over : CF-hom n ⊙Σbwin == ×ᴳ-inl
                [ (λ G → GroupHom (C n (⊙BigWedge Y)) G) ↓ path ]
  ⊙Σbwin-over = SER.φ-over-iso

  ⊙select-over : CF-hom n ⊙select == ×ᴳ-snd {G = C n (⊙BigWedge Y)}
                 [ (λ G → GroupHom G (C n X)) ↓ path ]
  ⊙select-over = SER.ψ-over-iso

  open CofSelect public using (select; ⊙select; ⊙Σbwin)
-}
