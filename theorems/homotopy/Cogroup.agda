{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CoHSpace

module homotopy.Cogroup {i} where

record CogroupStructure (X : Ptd i) : Type i where
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

module _ {X : Ptd i} (cogroup-struct : CogroupStructure X)
  {j} (Y : Ptd j) where

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

  cogroup⊙→-group-structure : GroupStructure (X ⊙→ Y)
  cogroup⊙→-group-structure = record
    { ident = ⊙cst
    ; inv = inv
    ; comp = comp
    ; unit-l = unit-l
    ; assoc = assoc
    ; inv-l = inv-l
    }

module _ (X : Ptd i) where

  private
    ⊙inv = ⊙Susp-flip X

    abstract
      inv-l : ∀ σ → ⊙WedgeRec.f (⊙Susp-flip X) (⊙idf (⊙Susp X)) (pinch X σ) == north
      inv-l = Susp-elim (! (merid (pt X))) (! (merid (pt X))) λ x →
        ↓-app=cst-in $ ! $ ap (_∙ ! (merid (pt X))) $
          ap (W.f ∘ pinch X) (merid x)
            =⟨ ap-∘ W.f (pinch X) (merid x) ⟩
          ap W.f (ap (pinch X) (merid x))
            =⟨ ap (ap W.f) (Pinch.merid-β X x) ⟩
          ap W.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
            =⟨ ap-∙∙ W.f (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
          ap W.f (ap winl (σloop X x)) ∙ ap W.f wglue ∙ ap W.f (ap winr (merid x))
            =⟨ ap3 (λ p q r → p ∙ q ∙ r)
                ( ∘-ap W.f winl (σloop X x)
                ∙ ap-∙ Susp-flip (merid x) (! (merid (pt X)))
                ∙ (SuspFlip.merid-β x ∙2 (ap-! Susp-flip (merid (pt X)) ∙ ap ! (SuspFlip.merid-β (pt X)))))
                (W.glue-β ∙ ∙-unit-r (! (merid (pt X))))
                (∘-ap W.f winr (merid x) ∙ ap-idf (merid x)) ⟩
          (! (merid x) ∙ ! (! (merid (pt X)))) ∙ (! (merid (pt X)) ∙ merid x)
            =⟨ ap (_∙ (! (merid (pt X)) ∙ merid x)) (∙-! (merid x) (! (merid (pt X)))) ⟩
          ! (! (merid (pt X)) ∙ merid x) ∙ (! (merid (pt X)) ∙ merid x)
            =⟨ !-inv-l (! (merid (pt X)) ∙ merid x) ⟩
          idp
            =∎
        where module W = ⊙WedgeRec (⊙Susp-flip X) (⊙idf (⊙Susp X))

      ⊙inv-l : ⊙Wedge-rec (⊙Susp-flip X) (⊙idf (⊙Susp X)) ⊙∘ ⊙pinch X ⊙∼ ⊙cst
      ⊙inv-l = inv-l , ↓-idf=cst-in' idp

      assoc : ∀ σ
        → fst (⊙–> (⊙∨-assoc (⊙Susp X) (⊙Susp X) (⊙Susp X)))
            (∨-fmap (⊙pinch X) (⊙idf (⊙Susp X)) (pinch X σ))
        == ∨-fmap (⊙idf (⊙Susp X)) (⊙pinch X) (pinch X σ)
      assoc = Susp-elim idp idp λ x → ↓-='-in' $ ! $
        ap (Assoc.f ∘ FmapL.f ∘ pinch X) (merid x)
          =⟨ ap-∘ (Assoc.f ∘ FmapL.f) (pinch X) (merid x) ⟩
        ap (Assoc.f ∘ FmapL.f) (ap (pinch X) (merid x))
          =⟨ ap (ap (Assoc.f ∘ FmapL.f)) (Pinch.merid-β X x) ⟩
        ap (Assoc.f ∘ FmapL.f) (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
          =⟨ ap-∘ Assoc.f FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)) ⟩
        ap Assoc.f (ap FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)))
          =⟨ ap (ap Assoc.f) $
                ap FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
                  =⟨ ap-∙∙ FmapL.f (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
                ap FmapL.f (ap winl (σloop X x)) ∙ ap FmapL.f wglue ∙ ap FmapL.f (ap winr (merid x))
                  =⟨ ap3 (λ p q r → p ∙ q ∙ r)
                      ( ∘-ap FmapL.f winl (σloop X x)
                      ∙ ap-∘ winl (pinch X) (σloop X x)
                      ∙ ap (ap winl) (lemma₀ x)
                      ∙ ap-∙∙∙ winl (ap winl (σloop X x)) wglue (ap winr (σloop X x)) (! wglue)
                      ∙ ap3 (λ p q r → p ∙ ap winl wglue ∙ q ∙ r)
                          (∘-ap winl winl (σloop X x))
                          (∘-ap winl winr (σloop X x))
                          (ap-! winl wglue))
                      FmapL.glue-β
                      (∘-ap FmapL.f winr (merid x)) ⟩
                ( ap (winl ∘ winl) (σloop X x) ∙ ap winl wglue ∙ ap (winl ∘ winr) (σloop X x) ∙ ! (ap winl wglue))
                ∙ wglue ∙ ap winr (merid x)
                  =∎ ⟩
        ap Assoc.f
          ((ap (winl ∘ winl) (σloop X x) ∙ ap winl wglue ∙ ap (winl ∘ winr) (σloop X x) ∙ ! (ap winl wglue))
           ∙ wglue ∙ ap winr (merid x))
          =⟨ ap-∙∙ Assoc.f
              (ap (winl ∘ winl) (σloop X x) ∙ ap winl wglue ∙ ap (winl ∘ winr) (σloop X x) ∙ ! (ap winl wglue))
              wglue (ap winr (merid x))
           ∙ ap (λ p → p ∙ ap Assoc.f wglue ∙ ap Assoc.f (ap winr (merid x)))
              (ap-∙∙∙ Assoc.f
                (ap (winl ∘ winl) (σloop X x))
                (ap winl wglue)
                (ap (winl ∘ winr) (σloop X x))
                (! (ap winl wglue))) ⟩
        ( ap Assoc.f (ap (winl ∘ winl) (σloop X x))
        ∙ ap Assoc.f (ap winl wglue)
        ∙ ap Assoc.f (ap (winl ∘ winr) (σloop X x))
        ∙ ap Assoc.f (! (ap winl wglue)))
          ∙ ap Assoc.f wglue ∙ ap Assoc.f (ap winr (merid x))
          =⟨ ap6 (λ p₀ p₁ p₂ p₃ p₄ p₅ → (p₀ ∙ p₁ ∙ p₂ ∙ p₃) ∙ p₄ ∙ p₅)
              (∘-ap Assoc.f (winl ∘ winl) (σloop X x))
              (∘-ap Assoc.f winl wglue ∙ AssocInl.glue-β)
              (∘-ap Assoc.f (winl ∘ winr) (σloop X x) ∙ ap-∘ winr winl (σloop X x))
              (ap-! Assoc.f (ap winl wglue) ∙ ap ! (∘-ap Assoc.f winl wglue ∙ AssocInl.glue-β))
              Assoc.glue-β
              (∘-ap Assoc.f winr (merid x) ∙ ap-∘ winr winr (merid x)) ⟩
        (ap winl (σloop X x) ∙ wglue ∙ ap winr (ap winl (σloop X x)) ∙ ! wglue)
        ∙ (wglue ∙ ap winr wglue) ∙ ap winr (ap winr (merid x))
          =⟨ lemma₁ (ap winl (σloop X x)) wglue (ap winr (ap winl (σloop X x))) (ap winr wglue) (ap winr (ap winr (merid x))) ⟩
        ap winl (σloop X x) ∙ wglue ∙ ap winr (ap winl (σloop X x)) ∙ ap winr wglue ∙ ap winr (ap winr (merid x))
          =⟨ ap3 (λ p q r → p ∙ q ∙ r)
              (ap-∘ FmapR.f winl (σloop X x))
              (! FmapR.glue-β)
              ( ∙∙-ap winr (ap winl (σloop X x)) wglue (ap winr (merid x))
              ∙ ap (ap winr) (! (Pinch.merid-β X x))
              ∙ ∘-ap winr (pinch X) (merid x)
              ∙ ap-∘ FmapR.f winr (merid x)) ⟩
        ap FmapR.f (ap winl (σloop X x)) ∙ ap FmapR.f wglue ∙ ap FmapR.f (ap winr (merid x))
          =⟨ ∙∙-ap FmapR.f (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
        ap FmapR.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
          =⟨ ! $ ap (ap FmapR.f) (Pinch.merid-β X x) ⟩
        ap FmapR.f (ap (pinch X) (merid x))
          =⟨ ∘-ap FmapR.f (pinch X) (merid x) ⟩
        ap (FmapR.f ∘ pinch X) (merid x)
          =∎
        where
          module Assoc = WedgeAssoc (⊙Susp X) (⊙Susp X) (⊙Susp X)
          module AssocInl = WedgeAssocInl (⊙Susp X) (⊙Susp X) (⊙Susp X)
          module FmapL = WedgeFmap (⊙pinch X) (⊙idf (⊙Susp X))
          module FmapR = WedgeFmap (⊙idf (⊙Susp X)) (⊙pinch X)

          lemma₀ : ∀ x → ap (pinch X) (σloop X x)
            == ap winl (σloop X x) ∙ wglue ∙ ap winr (σloop X x) ∙ ! wglue
          lemma₀ x =
            ap (pinch X) (σloop X x)
              =⟨ ap-∙ (pinch X) (merid x) (! (merid (pt X))) ⟩
            ap (pinch X) (merid x) ∙ ap (pinch X) (! (merid (pt X)))
              =⟨ Pinch.merid-β X x ∙2 (ap-! (pinch X) (merid (pt X)) ∙ ap ! (Pinch.merid-β X (pt X))) ⟩
            (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)) ∙ ! (ap winl (σloop X (pt X)) ∙ wglue ∙ ap winr (merid (pt X)))
              =⟨ ap (λ p → (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
                           ∙ ! (ap winl p ∙ wglue ∙ ap winr (merid (pt X))))
                    σloop-pt ⟩
            (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)) ∙ ! (wglue ∙ ap winr (merid (pt X)))
              =⟨ lemma₀₁ winr (ap winl (σloop X x)) wglue (merid x) (merid (pt X)) ⟩
            ap winl (σloop X x) ∙ wglue ∙ ap winr (σloop X x) ∙ ! wglue
              =∎
            where
              lemma₀₁ : ∀ {i j} {A : Type i} {B : Type j} {b₀ b₁ : B} {a₂ a₃ : A}
                → (f : A → B)
                → (p₀ : b₀ == b₁) (p₁ : b₁ == f a₂) (p₂ : a₂ == a₃) (p₃ : a₂ == a₃)
                → (p₀ ∙ p₁ ∙ ap f p₂) ∙ ! (p₁ ∙ ap f p₃)
                == p₀ ∙ p₁ ∙ ap f (p₂ ∙ ! p₃) ∙ ! p₁
              lemma₀₁ f idp idp idp p₃ = !-ap f p₃ ∙ ! (∙-unit-r (ap f (! p₃)))

          lemma₁ : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ a₄ : A}
            → (p₀ : a₀ == a₁) (p₁ : a₁ == a₂) (p₂ : a₂ == a₂) (p₃ : a₂ == a₃) (p₄ : a₃ == a₄)
            → (p₀ ∙ p₁ ∙ p₂ ∙ ! p₁) ∙ (p₁ ∙ p₃) ∙ p₄
            == p₀ ∙ p₁ ∙ (p₂ ∙ p₃ ∙ p₄)
          lemma₁ idp idp p₂ idp idp = ∙-unit-r (p₂ ∙ idp)

      ⊙assoc :
           ⊙–> (⊙∨-assoc (⊙Susp X) (⊙Susp X) (⊙Susp X)) ⊙∘
           ⊙∨-fmap (⊙pinch X) (⊙idf (⊙Susp X)) ⊙∘ ⊙pinch X
        ⊙∼ ⊙∨-fmap (⊙idf (⊙Susp X)) (⊙pinch X) ⊙∘ ⊙pinch X
      ⊙assoc = assoc , idp

  Susp-cogroup-structure : CogroupStructure (⊙Susp X)
  Susp-cogroup-structure = record {
    co-h-struct = Susp-co-h-space-structure X;
    ⊙inv = ⊙Susp-flip X;
    ⊙inv-l = ⊙inv-l;
    ⊙assoc = ⊙assoc}

  Susp⊙→-group-structure : ∀ {j} (Y : Ptd j) → GroupStructure (⊙Susp X ⊙→ Y)
  Susp⊙→-group-structure Y = cogroup⊙→-group-structure Susp-cogroup-structure Y
