{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Cogroup
open import cohomology.Theory

-- H^n is a group homomorphism when the domain is (Susp X -> Y).
module cohomology.Cogroup {i} (CT : CohomologyTheory i) (n : ℤ)
  {X : Ptd i} (cogroup-struct : CogroupStructure X) (Y : Ptd i) where

  open CohomologyTheory CT
  open import cohomology.Wedge CT
  open CogroupStructure cogroup-struct
  open import cohomology.CoHSpace CT n co-h-struct

  private
    module dom = GroupStructure (cogroup⊙→-group-structure cogroup-struct Y)
    module codom = Group (hom-group (C n Y) (C-abgroup n X))

  C-fmap-preserves-comp : preserves-comp dom.comp codom.comp (C-fmap n)
  C-fmap-preserves-comp f g = group-hom= $ λ= λ y →
    CEl-fmap n (dom.comp f g) y
      =⟨ C-fmap-∘ n (⊙Wedge-rec f g) ⊙coμ y ⟩
    CEl-fmap n ⊙coμ (CEl-fmap n (⊙Wedge-rec f g) y)
      =⟨ C-fmap-coμ (CEl-fmap n (⊙Wedge-rec f g) y) ⟩
    Group.comp (C n X)
      (CEl-fmap n ⊙winl (CEl-fmap n (⊙Wedge-rec f g) y))
      (CEl-fmap n ⊙winr (CEl-fmap n (⊙Wedge-rec f g) y))
      =⟨ ap2 (Group.comp (C n X))
           ( ∘-CEl-fmap n ⊙winl (⊙Wedge-rec f g) y
           ∙ ap (λ f → CEl-fmap n f y) (⊙WedgeRec.⊙winl-β f g))
           ( ∘-CEl-fmap n ⊙winr (⊙Wedge-rec f g) y
           ∙ ap (λ f → CEl-fmap n f y) (⊙WedgeRec.⊙winr-β f g)) ⟩
    Group.comp (C n X) (CEl-fmap n f y) (CEl-fmap n g y)
      =∎
