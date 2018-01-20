{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.CoHSpace where

record CoHSpaceStructure {i} (X : Ptd i) : Type i where
  constructor coHSpaceStructure
  field
    ⊙coμ : X ⊙→ X ⊙∨ X

  coμ : de⊙ X → X ∨ X
  coμ = fst ⊙coμ

  field
    ⊙unit-l : ⊙projr ⊙∘ ⊙coμ ⊙∼ ⊙idf X
    ⊙unit-r : ⊙projl ⊙∘ ⊙coμ ⊙∼ ⊙idf X

module _ {i j : ULevel} {X : Ptd i} (CHSS : CoHSpaceStructure X) where

  open CoHSpaceStructure CHSS

  private
    lemma-l : ⊙projr ⊙∘ ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j}) ⊙∘ ⊙coμ ⊙∘ ⊙lower {j = j}
           == ⊙idf _
  abstract
    lemma-l =
        ! (⊙λ= (⊙∘-assoc ⊙projr (⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j})) (⊙coμ ⊙∘ ⊙lower {j = j})))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (⊙λ= (⊙Wedge-rec-fmap ⊙cst (⊙idf _) (⊙lift {j = j}) (⊙lift {j = j})))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (! (⊙λ= (⊙Wedge-rec-post∘ (⊙lift {j = j}) ⊙cst (⊙idf _))))
      ∙ ⊙λ= (⊙∘-assoc (⊙lift {j = j}) ⊙projr (⊙coμ ⊙∘ ⊙lower {j = j}))
      ∙ ap (λ f → ⊙lift {j = j} ⊙∘ f ⊙∘ ⊙lower {j = j}) (⊙λ= ⊙unit-l)

  private
    lemma-r : ⊙projl ⊙∘ ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j}) ⊙∘ ⊙coμ ⊙∘ ⊙lower {j = j}
           == ⊙idf _
  abstract
    lemma-r =
        ! (⊙λ= (⊙∘-assoc ⊙projl (⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j})) (⊙coμ ⊙∘ ⊙lower {j = j})))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (⊙λ= (⊙Wedge-rec-fmap (⊙idf _) ⊙cst (⊙lift {j = j}) (⊙lift {j = j})))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (! (⊙λ= (⊙Wedge-rec-post∘ (⊙lift {j = j}) (⊙idf _) ⊙cst)))
      ∙ ⊙λ= (⊙∘-assoc (⊙lift {j = j}) ⊙projl (⊙coμ ⊙∘ ⊙lower {j = j}))
      ∙ ap (λ f → ⊙lift {j = j} ⊙∘ f ⊙∘ ⊙lower {j = j}) (⊙λ= ⊙unit-r)

  Lift-co-h-space-structure : CoHSpaceStructure (⊙Lift {j = j} X)
  Lift-co-h-space-structure = record
    { ⊙coμ = ⊙∨-fmap ⊙lift ⊙lift ⊙∘ ⊙coμ ⊙∘ ⊙lower
    ; ⊙unit-l = ⊙app= lemma-l
    ; ⊙unit-r = ⊙app= lemma-r
    }
