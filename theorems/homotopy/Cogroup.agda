{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CoHSpace

module homotopy.Cogroup {i} {X : Ptd i} where

record CogroupStructure : Type i where
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

module MapsFromCogroup (cogroup-struct : CogroupStructure)
  {j} (Y : Ptd j) where

  module CGS = CogroupStructure cogroup-struct
  ⊙coμ = CGS.⊙coμ

  private
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
          =⟨ ap (_⊙∘ ⊙coμ) (! (⊙Wedge-rec-post∘ f ⊙cst (⊙idf X))) ⟩
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
          =⟨ ! $ ⊙λ= (⊙∘-Wedge-rec-fmap (⊙Wedge-rec f g) h ⊙coμ (⊙idf X)) |in-ctx _⊙∘ ⊙coμ ⟩
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
          =⟨ ⊙λ= (⊙∘-Wedge-rec-fmap f (⊙Wedge-rec g h) (⊙idf X) ⊙coμ) |in-ctx _⊙∘ ⊙coμ  ⟩
        ⊙Wedge-rec (f ⊙∘ ⊙idf X) (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ
          =⟨ ⊙λ= (⊙∘-unit-r f) |in-ctx (λ f → ⊙Wedge-rec f (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ) ⟩
        ⊙Wedge-rec f (⊙Wedge-rec g h ⊙∘ ⊙coμ) ⊙∘ ⊙coμ
          =∎

      inv-l : ∀ f → comp (inv f) f == ⊙cst
      inv-l f =
        ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) f ⊙∘ ⊙coμ
          =⟨ ap (λ g → ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) g ⊙∘ ⊙coμ) (! $ ⊙λ= (⊙∘-unit-r f)) ⟩
        ⊙Wedge-rec (f ⊙∘ CGS.⊙inv) (f ⊙∘ ⊙idf X) ⊙∘ ⊙coμ
          =⟨ ap (_⊙∘ ⊙coμ) (! (⊙Wedge-rec-post∘ f CGS.⊙inv (⊙idf X))) ⟩
        (f ⊙∘ ⊙Wedge-rec CGS.⊙inv (⊙idf X)) ⊙∘ ⊙coμ
          =⟨ ⊙λ= $ ⊙∘-assoc f (⊙Wedge-rec CGS.⊙inv (⊙idf X)) ⊙coμ ⟩
        f ⊙∘ (⊙Wedge-rec CGS.⊙inv (⊙idf X) ⊙∘ ⊙coμ)
          =⟨ ap (f ⊙∘_) (⊙λ= CGS.⊙inv-l) ⟩
        f ⊙∘ ⊙cst
          =⟨ ⊙λ= (⊙∘-cst-r f) ⟩
        ⊙cst
          =∎

  maps-from-cogroup-group-structure : GroupStructure (X ⊙→ Y)
  maps-from-cogroup-group-structure = record
    { ident = ⊙cst
    ; inv = inv
    ; comp = comp
    ; unit-l = unit-l
    ; assoc = assoc
    ; inv-l = inv-l
    }
