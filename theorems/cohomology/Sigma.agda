{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdMapSequence
open import homotopy.CofiberSequence
open import groups.Exactness
open import groups.ExactSequence
open import groups.HomSequence
open import cohomology.Theory

module cohomology.Sigma {i} (CT : CohomologyTheory i)
  (n : ℤ) (X : Ptd i) (Y : de⊙ X → Ptd i) where

open CohomologyTheory CT
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
  abstract
    cst-C-Σbwin-is-exact : is-exact (cst-hom {G = C n (⊙Susp X)}) (C-fmap n ⊙Σbwin)
    cst-C-Σbwin-is-exact = equiv-preserves-exact
      {φ₁ = cst-hom {G = C n (⊙Susp X)}}
      {ξG = C-fmap n (⊙Susp-to-⊙Cof² ⊙select)} {ξH = idhom _} {ξK = idhom _}
      (comm-sqrᴳ λ x →
        CEl-fmap n (⊙cfcod²' ⊙select) x
          =⟨ ! $ CEl-fmap-idf n $ CEl-fmap n (⊙cfcod²' ⊙select) x ⟩
        CEl-fmap n (⊙idf _) (CEl-fmap n (⊙cfcod²' ⊙select) x)
          =⟨ C-comm-square n (extract-glue-cod²-comm-sqr ⊙select) □$ᴳ x ⟩
        CEl-fmap n ⊙extract-glue (CEl-fmap n (⊙Susp-to-⊙Cof² ⊙select) x)
          =⟨ CEl-fmap-const n (extract-glue-from-BigWedge-is-const Y) _ ⟩
        Cident n _
          =∎)
      (comm-sqrᴳ λ _ → idp)
      (C-isemap n (⊙Susp-to-⊙Cof² ⊙select) (snd (Cof²-equiv-Susp ⊙select ⁻¹)))
      (idf-is-equiv _)
      (idf-is-equiv _)
      (C-exact n ⊙Σbwin)

  χ : C n X →ᴳ C n (⊙Σ X Y)
  χ = C-fmap n (⊙fstᵈ Y)

  abstract
    select-χ-is-idf : ∀ s → CEl-fmap n ⊙select (GroupHom.f χ s) == s
    select-χ-is-idf = CEl-fmap-inverse n ⊙select (⊙fstᵈ Y) λ _ → idp

C-Σ : C n (⊙Σ X Y) ≃ᴳ C n (⊙BigWedge Y) ×ᴳ C n X
C-Σ = Exact.φ-inj-and-ψ-has-rinv-split
  (C-exact n ⊙select) (C-is-abelian n _)
  (Exact.φ-const-implies-ψ-is-inj cst-C-Σbwin-is-exact (λ _ → idp))
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
