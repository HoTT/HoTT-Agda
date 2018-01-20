{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CoHSpace
open import cohomology.Theory

module cohomology.CoHSpace {i} (CT : CohomologyTheory i) (n : ℤ)
  {X : Ptd i} (CHSS : CoHSpaceStructure X) where

open CohomologyTheory CT
open CoHSpaceStructure CHSS
open import cohomology.Wedge CT n

private
  lemma-l : CEl-fmap n ⊙coμ ∘ CEl-fmap n ⊙projl ∼ idf _
  lemma-l x =
      ∘-CEl-fmap n ⊙coμ ⊙projl x
    ∙ ap (λ f → CEl-fmap n f x) (⊙λ= ⊙unit-r)
    ∙ CEl-fmap-idf n x
  
  lemma-r : CEl-fmap n ⊙coμ ∘ CEl-fmap n ⊙projr ∼ idf _
  lemma-r x =
      ∘-CEl-fmap n ⊙coμ ⊙projr x
    ∙ ap (λ f → CEl-fmap n f x) (⊙λ= ⊙unit-l)
    ∙ CEl-fmap-idf n x

C-fmap-coμ : ∀ x → CEl-fmap n ⊙coμ x == Group.comp (C n X) (CEl-fmap n ⊙winl x) (CEl-fmap n ⊙winr x)
C-fmap-coμ x =
  CEl-fmap n ⊙coμ x
    =⟨ C-Wedge-out-η-comm-sqr X X (C-fmap n ⊙coμ) □$ᴳ x ⟩
  Group.comp (C n X)
    (CEl-fmap n ⊙coμ (CEl-fmap n ⊙projl (CEl-fmap n ⊙winl x)))
    (CEl-fmap n ⊙coμ (CEl-fmap n ⊙projr (CEl-fmap n ⊙winr x)))
    =⟨ ap2 (Group.comp (C n X)) (lemma-l (CEl-fmap n ⊙winl x)) (lemma-r (CEl-fmap n ⊙winr x)) ⟩
  Group.comp (C n X) (CEl-fmap n ⊙winl x) (CEl-fmap n ⊙winr x)
    =∎
