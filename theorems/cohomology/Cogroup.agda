{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Cogroup
open import cohomology.Theory

-- H^n is a group homomorphism when the domain is (Susp X -> Y).
module cohomology.Cogroup {i} (CT : CohomologyTheory i) (n : ℤ)
  {X : Ptd i} (cogroup-struct : CogroupStructure X) (Y : Ptd i) where

  open CohomologyTheory CT
  open import cohomology.Wedge CT

  private
    module cogroup = CogroupStructure cogroup-struct
    module dom = GroupStructure (cogroup⊙→-group-structure cogroup-struct Y)
    module codom = Group (hom-group (C n Y) (C-abgroup n X))
    ⊙coμ = cogroup.⊙coμ

  C-fmap-preserves-comp : preserves-comp dom.comp codom.comp (C-fmap n)
  C-fmap-preserves-comp f g = group-hom= $ λ= λ y →
    CEl-fmap n (dom.comp f g) y
      =⟨ C-fmap-∘ n (⊙Wedge-rec f g) ⊙coμ y ⟩
    CEl-fmap n ⊙coμ (CEl-fmap n (⊙Wedge-rec f g) y)
      =⟨ ! $ ap (λ f → CEl-fmap n ⊙coμ (CEl-fmap n f y)) $ ⊙λ= $ ⊙fold-fmap f g ⟩
    CEl-fmap n ⊙coμ (CEl-fmap n (⊙fold ⊙∘ ⊙Wedge-fmap f g) y)
      =⟨ ap (CEl-fmap n ⊙coμ) (CEl-fmap-∘ n ⊙fold (⊙Wedge-fmap f g) y) ⟩
    CEl-fmap n ⊙coμ (CEl-fmap n (⊙Wedge-fmap f g) (CEl-fmap n ⊙fold y))
      =⟨ ∘-CEl-fmap n ⊙coμ (⊙Wedge-fmap f g) (CEl-fmap n ⊙fold y) ⟩
    CEl-fmap n (⊙Wedge-fmap f g ⊙∘ ⊙coμ) (CEl-fmap n ⊙fold y)
      =⟨ ! $ ap (CEl-fmap n (⊙Wedge-fmap f g ⊙∘ ⊙coμ))
                (C-fold-comm-sqr' n Y □$ᴳ y) ⟩
    CEl-fmap n (⊙Wedge-fmap f g ⊙∘ ⊙coμ) (GroupIso.g (C-Wedge n Y Y) (y , y))
      =⟨ ! (C-Wedge-in-comm-sqr' n Y Y (⊙Wedge-fmap f g ⊙∘ ⊙coμ) □$ᴳ (y , y)) ⟩
    Group.comp (C n X)
      (CEl-fmap n (⊙projl ⊙∘ (⊙Wedge-fmap f g ⊙∘ ⊙coμ)) y)
      (CEl-fmap n (⊙projr ⊙∘ (⊙Wedge-fmap f g ⊙∘ ⊙coμ)) y)
      =⟨ ap2 (Group.comp (C n X))
             (CEl-fmap-base-indep n (λ _ → idp) y)
             (CEl-fmap-base-indep n (λ _ → idp) y) ⟩
    Group.comp (C n X)
      (CEl-fmap n ((⊙projl ⊙∘ ⊙Wedge-fmap f g) ⊙∘ ⊙coμ) y)
      (CEl-fmap n ((⊙projr ⊙∘ ⊙Wedge-fmap f g) ⊙∘ ⊙coμ) y)
      =⟨ ap2 (λ f g → Group.comp (C n X) (CEl-fmap n (f ⊙∘ ⊙coμ) y) (CEl-fmap n (g ⊙∘ ⊙coμ) y))
             (⊙λ= $ ⊙projl-fmap f g)
             (⊙λ= $ ⊙projr-fmap f g) ⟩
    Group.comp (C n X)
      (CEl-fmap n (dom.comp f ⊙cst) y)
      (CEl-fmap n (dom.comp ⊙cst g) y)
      =⟨ ap2 (λ f g → (Group.comp (C n X)) (CEl-fmap n f y) (CEl-fmap n g y))
             (dom.unit-r f) (dom.unit-l g) ⟩
    Group.comp (C n X) (CEl-fmap n f y) (CEl-fmap n g y)
      =∎
