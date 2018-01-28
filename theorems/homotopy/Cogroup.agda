{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CoHSpace

module homotopy.Cogroup where

record CogroupStructure {i} (X : Ptd i) : Type i where
  field
    co-h-struct : CoHSpaceStructure X
    ⊙inv : X ⊙→ X
  open CoHSpaceStructure co-h-struct public

  inv : de⊙ X → de⊙ X
  inv = fst ⊙inv

  field
    ⊙inv-l : ⊙Wedge-rec ⊙inv (⊙idf X) ⊙∘ ⊙coμ ⊙∼ ⊙cst
    ⊙assoc : ⊙–> (⊙∨-assoc X X X) ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
          ⊙∼ ⊙∨-fmap (⊙idf X) ⊙coμ ⊙∘ ⊙coμ

{-
module _ {i j : ULevel} {X : Ptd i} (CGS : CogroupStructure X) where

  open CogroupStructure CGS

  private
    lemma-inv : ⊙Wedge-rec (⊙Lift-fmap ⊙inv) (⊙idf (⊙Lift {j = j} X))
             ⊙∘ ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j})
             ⊙∘ ⊙coμ
             ⊙∘ ⊙lower {j = j}
             == ⊙cst
  abstract
    lemma-inv =
        ! (⊙λ= (⊙∘-assoc
             (⊙Wedge-rec (⊙Lift-fmap ⊙inv) (⊙idf (⊙Lift {j = j} X)))
             (⊙∨-fmap ⊙lift ⊙lift)
             (⊙coμ ⊙∘ ⊙lower)))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (⊙λ= (⊙Wedge-rec-fmap (⊙Lift-fmap ⊙inv) (⊙idf _) ⊙lift ⊙lift))
      ∙ ap (_⊙∘ ⊙coμ ⊙∘ ⊙lower) (! (⊙λ= (⊙Wedge-rec-post∘ ⊙lift ⊙inv (⊙idf _))))
      ∙ ⊙λ= (⊙∘-assoc ⊙lift (⊙Wedge-rec ⊙inv (⊙idf X)) (⊙coμ ⊙∘ ⊙lower))
      ∙ ap ⊙Lift-fmap (⊙λ= ⊙inv-l)

  private
    ⊙coμ' : ⊙Lift {j = j} X ⊙→ ⊙Lift {j = j} X ⊙∨ ⊙Lift {j = j} X
    ⊙coμ' = ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j}) ⊙∘ ⊙coμ ⊙∘ ⊙lower {j = j}

  private
    lemma-assoc' :
         ⊙–> (⊙∨-assoc (⊙Lift {j = j} X) (⊙Lift {j = j} X) (⊙Lift {j = j} X))
         ⊙∘ ⊙∨-fmap ⊙coμ' (⊙idf (⊙Lift {j = j} X))
         ⊙∘ ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j}) ⊙∘ ⊙coμ
      == ⊙∨-fmap (⊙idf (⊙Lift {j = j} X)) ⊙coμ'
         ⊙∘ ⊙∨-fmap (⊙lift {j = j}) (⊙lift {j = j}) ⊙∘ ⊙coμ
  abstract
    lemma-assoc' =
      ⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X))
      ⊙∘ ⊙∨-fmap ⊙coμ' (⊙idf (⊙Lift {j = j} X))
      ⊙∘ ⊙∨-fmap ⊙lift ⊙lift ⊙∘ ⊙coμ
        =⟨ ! $ ap (⊙–> (⊙∨-assoc _ _ _) ⊙∘_) $ ⊙λ= $
             ⊙∘-assoc
              (⊙∨-fmap ⊙coμ' (⊙idf (⊙Lift X)))
              (⊙∨-fmap ⊙lift ⊙lift)
              ⊙coμ ⟩
      ⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X))
      ⊙∘ (⊙∨-fmap ⊙coμ' (⊙idf (⊙Lift X)) ⊙∘ ⊙∨-fmap ⊙lift ⊙lift)
      ⊙∘ ⊙coμ
        =⟨ ap (λ f → ⊙–> (⊙∨-assoc _ _ _ ) ⊙∘ f ⊙∘ ⊙coμ) $
               ! (⊙λ= $ ⊙∨-fmap-∘ ⊙coμ' ⊙lift (⊙idf (⊙Lift X)) ⊙lift)
               ∙ (⊙λ= $ ⊙∨-fmap-∘ (⊙∨-fmap ⊙lift ⊙lift) ⊙coμ ⊙lift (⊙idf X)) ⟩
      ⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X))
      ⊙∘ (⊙∨-fmap (⊙∨-fmap ⊙lift ⊙lift) ⊙lift ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X))
      ⊙∘ ⊙coμ
        =⟨ ap (⊙–> (⊙∨-assoc _ _ _ ) ⊙∘_) $ ⊙λ= $
            ⊙∘-assoc
              (⊙∨-fmap (⊙∨-fmap ⊙lift ⊙lift) ⊙lift)
              (⊙∨-fmap ⊙coμ (⊙idf X))
              ⊙coμ ⟩
      ⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X))
      ⊙∘ ⊙∨-fmap (⊙∨-fmap ⊙lift ⊙lift) ⊙lift
      ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
        =⟨ ! $ ⊙λ= $
            ⊙∘-assoc
              (⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X)))
              (⊙∨-fmap (⊙∨-fmap ⊙lift ⊙lift) ⊙lift)
              (⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ) ⟩
      (⊙–> (⊙∨-assoc (⊙Lift X) (⊙Lift X) (⊙Lift X)) ⊙∘ ⊙∨-fmap (⊙∨-fmap ⊙lift ⊙lift) ⊙lift)
      ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
        =⟨ ap (_⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ) $
            ⊙λ= $ ⊙∨-assoc-nat ⊙lift ⊙lift ⊙lift ⟩
      (⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift) ⊙∘ ⊙–> (⊙∨-assoc X X X))
      ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
        =⟨ ⊙λ= $ ⊙∘-assoc
            (⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift))
            (⊙–> (⊙∨-assoc X X X))
            (⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ) ⟩
      ⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift)
      ⊙∘ ⊙–> (⊙∨-assoc X X X) ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
        =⟨ ap (⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift) ⊙∘_) $ ⊙λ= ⊙assoc ⟩
      ⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift)
      ⊙∘ ⊙∨-fmap (⊙idf X) ⊙coμ ⊙∘ ⊙coμ
        =⟨ ! $ ⊙λ= $ ⊙∘-assoc
            (⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift))
            (⊙∨-fmap (⊙idf X) ⊙coμ)
            ⊙coμ ⟩
      (⊙∨-fmap ⊙lift (⊙∨-fmap ⊙lift ⊙lift)
       ⊙∘ ⊙∨-fmap (⊙idf X) ⊙coμ)
      ⊙∘ ⊙coμ
        =⟨ ap (_⊙∘ ⊙coμ) $
             ! (⊙λ= $ ⊙∨-fmap-∘ ⊙lift (⊙idf X) (⊙∨-fmap ⊙lift ⊙lift) ⊙coμ)
             ∙ (⊙λ= $ ⊙∨-fmap-∘ (⊙idf (⊙Lift X)) ⊙lift ⊙coμ' ⊙lift) ⟩
      (⊙∨-fmap (⊙idf (⊙Lift X)) ⊙coμ' ⊙∘ ⊙∨-fmap ⊙lift ⊙lift) ⊙∘ ⊙coμ
        =⟨ ⊙λ= $ ⊙∘-assoc (⊙∨-fmap (⊙idf (⊙Lift X)) ⊙coμ') (⊙∨-fmap ⊙lift ⊙lift) ⊙coμ ⟩
      ⊙∨-fmap (⊙idf (⊙Lift X)) ⊙coμ' ⊙∘ ⊙∨-fmap ⊙lift ⊙lift ⊙∘ ⊙coμ
        =∎

  private
    lemma-assoc :
         ⊙–> (⊙∨-assoc (⊙Lift {j = j} X) (⊙Lift {j = j} X) (⊙Lift {j = j} X))
         ⊙∘ ⊙∨-fmap ⊙coμ' (⊙idf (⊙Lift {j = j} X)) ⊙∘ ⊙coμ'
      == ⊙∨-fmap (⊙idf (⊙Lift {j = j} X)) ⊙coμ' ⊙∘ ⊙coμ'
  abstract
    lemma-assoc = ap (_⊙∘ ⊙lower) lemma-assoc'

  Lift-cogroup-structure : CogroupStructure (⊙Lift {j = j} X)
  Lift-cogroup-structure = record
    { co-h-struct = Lift-co-h-space-structure {j = j} co-h-struct
    ; ⊙inv = ⊙lift ⊙∘ ⊙inv ⊙∘ ⊙lower
    ; ⊙inv-l = ⊙app= lemma-inv
    ; ⊙assoc = ⊙app= lemma-assoc
    }
-}

module _ {i j} {X : Ptd i} (cogroup-struct : CogroupStructure X) (Y : Ptd j) where

  private
    module CGS = CogroupStructure cogroup-struct
    ⊙coμ = CGS.⊙coμ

    comp : (X ⊙→ Y) → (X ⊙→ Y) → (X ⊙→ Y)
    comp f g = ⊙Wedge-rec f g ⊙∘ ⊙coμ

    inv : (X ⊙→ Y) → (X ⊙→ Y)
    inv = _⊙∘ CGS.⊙inv

    abstract
      unit-l : ∀ f → comp ⊙cst f == f
      unit-l f =
        ⊙Wedge-rec ⊙cst f ⊙∘ ⊙coμ
          =⟨ ap2 (λ f g → ⊙Wedge-rec f g ⊙∘ ⊙coμ) (! $ ⊙λ= (⊙∘-cst-r f)) (! $ ⊙λ= (⊙∘-unit-r f)) ⟩
        ⊙Wedge-rec (f ⊙∘ ⊙cst) (f ⊙∘ ⊙idf X) ⊙∘ ⊙coμ
          =⟨ ap (_⊙∘ ⊙coμ) (! $ ⊙λ= $ ⊙Wedge-rec-post∘ f ⊙cst (⊙idf X)) ⟩
        (f ⊙∘ ⊙Wedge-rec ⊙cst (⊙idf X)) ⊙∘ ⊙coμ
          =⟨ ⊙λ= $ ⊙∘-assoc f (⊙Wedge-rec ⊙cst (⊙idf X)) ⊙coμ ⟩
        f ⊙∘ (⊙Wedge-rec ⊙cst (⊙idf X) ⊙∘ ⊙coμ)
          =⟨ ap (f ⊙∘_) (⊙λ= CGS.⊙unit-l) ⟩
        f ⊙∘ ⊙idf X
          =⟨ ⊙λ= (⊙∘-unit-r f) ⟩
        f
          =∎

      assoc : ∀ f g h → comp (comp f g) h == comp f (comp g h)
      assoc f g h =
        ⊙Wedge-rec (⊙Wedge-rec f g ⊙∘ ⊙coμ) h ⊙∘ ⊙coμ
          =⟨ ! $ ⊙λ= (⊙∘-unit-r h) |in-ctx (λ h → ⊙Wedge-rec (⊙Wedge-rec f g ⊙∘ ⊙coμ) h ⊙∘ ⊙coμ) ⟩
        ⊙Wedge-rec (⊙Wedge-rec f g ⊙∘ ⊙coμ) (h ⊙∘ ⊙idf X) ⊙∘ ⊙coμ
          =⟨ ! $ ⊙λ= (⊙Wedge-rec-fmap (⊙Wedge-rec f g) h ⊙coμ (⊙idf X)) |in-ctx _⊙∘ ⊙coμ ⟩
        (⊙Wedge-rec (⊙Wedge-rec f g) h ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X)) ⊙∘ ⊙coμ
          =⟨ ⊙λ= $ ⊙∘-assoc (⊙Wedge-rec (⊙Wedge-rec f g) h) (⊙∨-fmap ⊙coμ (⊙idf X)) ⊙coμ ⟩
        ⊙Wedge-rec (⊙Wedge-rec f g) h ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
          =⟨ ⊙λ= (⊙Wedge-rec-assoc f g h) |in-ctx _⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ ⟩
        (⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘ ⊙–> (⊙∨-assoc X X X)) ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
          =⟨ ⊙λ= $ ⊙∘-assoc (⊙Wedge-rec f (⊙Wedge-rec g h)) (⊙–> (⊙∨-assoc X X X)) (⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ) ⟩
        ⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘ ⊙–> (⊙∨-assoc X X X) ⊙∘ ⊙∨-fmap ⊙coμ (⊙idf X) ⊙∘ ⊙coμ
          =⟨ ⊙λ= CGS.⊙assoc |in-ctx ⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘_ ⟩
        ⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘ ⊙∨-fmap (⊙idf X) ⊙coμ ⊙∘ ⊙coμ
          =⟨ ! $ ⊙λ= $ ⊙∘-assoc (⊙Wedge-rec f (⊙Wedge-rec g h)) (⊙∨-fmap (⊙idf X) ⊙coμ) ⊙coμ ⟩
        (⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘ ⊙∨-fmap (⊙idf X) ⊙coμ) ⊙∘ ⊙coμ
          =⟨ ⊙λ= (⊙Wedge-rec-fmap f (⊙Wedge-rec g h) (⊙idf X) ⊙coμ) |in-ctx _⊙∘ ⊙coμ  ⟩
        ⊙Wedge-rec (f ⊙∘ ⊙idf X) (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ
          =⟨ ⊙λ= (⊙∘-unit-r f) |in-ctx (λ f → ⊙Wedge-rec f (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ) ⟩
        ⊙Wedge-rec f (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ
          =∎

      inv-l : ∀ f → comp (inv f) f == ⊙cst
      inv-l f =
        ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) f ⊙∘ ⊙coμ
          =⟨ ap (λ g → ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) g ⊙∘ ⊙coμ) (! $ ⊙λ= (⊙∘-unit-r f)) ⟩
        ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) (f ⊙∘ ⊙idf X) ⊙∘ ⊙coμ
          =⟨ ap (_⊙∘ ⊙coμ) (! $ ⊙λ= $ ⊙Wedge-rec-post∘ f CGS.⊙inv (⊙idf X)) ⟩
        (f ⊙∘ ⊙Wedge-rec CGS.⊙inv (⊙idf X)) ⊙∘ ⊙coμ
          =⟨ ⊙λ= $ ⊙∘-assoc f (⊙Wedge-rec CGS.⊙inv (⊙idf X)) ⊙coμ ⟩
        f ⊙∘ (⊙Wedge-rec CGS.⊙inv (⊙idf X) ⊙∘ ⊙coμ)
          =⟨ ap (f ⊙∘_) (⊙λ= CGS.⊙inv-l) ⟩
        f ⊙∘ ⊙cst
          =⟨ ⊙λ= (⊙∘-cst-r f) ⟩
        ⊙cst
          =∎

  cogroup⊙→-group-structure : GroupStructure (X ⊙→ Y)
  cogroup⊙→-group-structure = record
    { ident = ⊙cst
    ; inv = inv
    ; comp = comp
    ; unit-l = unit-l
    ; assoc = assoc
    ; inv-l = inv-l
    }
