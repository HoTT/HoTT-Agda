{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CoHSpace
open import homotopy.Cogroup

module groups.FromSusp where

module _ {i} (X : Ptd i) where
  private
    A = de⊙ X
    e = pt X

  module Pinch = SuspRec (winl north) (winr south)
    (λ a → ap winl (σloop X a) ∙ wglue ∙ ap winr (merid a))

  pinch : Susp A → ⊙Susp X ∨ ⊙Susp X
  pinch = Pinch.f

  ⊙pinch : ⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X
  ⊙pinch = pinch , idp

  private
    abstract
      unit-r : ∀ x → projl (pinch x) == x
      unit-r = Susp-elim idp (merid e) λ x → ↓-∘=idf-in' projl pinch $
        ap projl (ap pinch (merid x)) ∙' merid e
          =⟨ ∙'=∙ (ap projl (ap pinch (merid x))) (merid e) ⟩
        ap projl (ap pinch (merid x)) ∙ merid e
          =⟨ ap (_∙ merid e) $
            ap projl (ap pinch (merid x))
              =⟨ ap (ap projl) $ Pinch.merid-β x ⟩
            ap projl (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
              =⟨ ap-∙∙ projl (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
            ap projl (ap winl (σloop X x)) ∙ ap projl wglue ∙ ap projl (ap winr (merid x))
              =⟨ ap3 (λ p q r → p ∙ q ∙ r)
                  (∘-ap projl winl (σloop X x) ∙ ap-idf (σloop X x))
                  Projl.glue-β
                  (∘-ap projl winr (merid x) ∙ ap-cst north (merid x)) ⟩
            σloop X x ∙ idp
              =⟨ ∙-unit-r (σloop X x) ⟩
            σloop X x
              =∎ ⟩
        σloop X x ∙ merid e
          =⟨ ∙-assoc (merid x) (! (merid e)) (merid e) ⟩
        merid x ∙ ! (merid e) ∙ merid e
          =⟨ ap (merid x ∙_) (!-inv-l (merid e)) ∙ ∙-unit-r (merid x) ⟩
        merid x
          =∎

      ⊙unit-r : ⊙projl ⊙∘ ⊙pinch ⊙∼ ⊙idf (⊙Susp X)
      ⊙unit-r = unit-r , idp

      unit-l : ∀ x → projr (pinch x) == x
      unit-l = Susp-elim idp idp λ x → ↓-∘=idf-in' projr pinch $
        ap projr (ap pinch (merid x))
          =⟨ ap (ap projr) $ Pinch.merid-β x ⟩
        ap projr (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
          =⟨ ap-∙∙ projr (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
        ap projr (ap winl (σloop X x)) ∙ ap projr wglue ∙ ap projr (ap winr (merid x))
          =⟨ ap3 (λ p q r → p ∙ q ∙ r)
              (∘-ap projr winl (σloop X x) ∙ ap-cst north (σloop X x))
              Projr.glue-β
              (∘-ap projr winr (merid x) ∙ ap-idf (merid x)) ⟩
        merid x
          =∎

      ⊙unit-l : ⊙projr ⊙∘ ⊙pinch ⊙∼ ⊙idf (⊙Susp X)
      ⊙unit-l = unit-l , idp

  Susp-co-h-space-structure : CoHSpaceStructure (⊙Susp X)
  Susp-co-h-space-structure = record {
    ⊙coμ = ⊙pinch;
    ⊙unit-l = ⊙unit-l;
    ⊙unit-r = ⊙unit-r}

  private
    ⊙inv = ⊙Susp-flip X

    abstract
      inv-l : ∀ σ → ⊙WedgeRec.f (⊙Susp-flip X) (⊙idf (⊙Susp X)) (pinch σ) == north
      inv-l = Susp-elim (! (merid (pt X))) (! (merid (pt X))) λ x →
        ↓-app=cst-in $ ! $ ap (_∙ ! (merid (pt X))) $
          ap (W.f ∘ pinch) (merid x)
            =⟨ ap-∘ W.f pinch (merid x) ⟩
          ap W.f (ap pinch (merid x))
            =⟨ ap (ap W.f) (Pinch.merid-β x) ⟩
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

      ⊙inv-l : ⊙Wedge-rec (⊙Susp-flip X) (⊙idf (⊙Susp X)) ⊙∘ ⊙pinch ⊙∼ ⊙cst
      ⊙inv-l = inv-l , ↓-idf=cst-in' idp

      assoc : ∀ σ
        → fst (⊙–> (⊙∨-assoc (⊙Susp X) (⊙Susp X) (⊙Susp X)))
            (∨-fmap ⊙pinch (⊙idf (⊙Susp X)) (pinch σ))
        == ∨-fmap (⊙idf (⊙Susp X)) ⊙pinch (pinch σ)
      assoc = Susp-elim idp idp λ x → ↓-='-in' $ ! $
        ap (Assoc.f ∘ FmapL.f ∘ pinch) (merid x)
          =⟨ ap-∘ (Assoc.f ∘ FmapL.f) pinch (merid x) ⟩
        ap (Assoc.f ∘ FmapL.f) (ap pinch (merid x))
          =⟨ ap (ap (Assoc.f ∘ FmapL.f)) (Pinch.merid-β x) ⟩
        ap (Assoc.f ∘ FmapL.f) (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
          =⟨ ap-∘ Assoc.f FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)) ⟩
        ap Assoc.f (ap FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x)))
          =⟨ ap (ap Assoc.f) $
                ap FmapL.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
                  =⟨ ap-∙∙ FmapL.f (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
                ap FmapL.f (ap winl (σloop X x)) ∙ ap FmapL.f wglue ∙ ap FmapL.f (ap winr (merid x))
                  =⟨ ap3 (λ p q r → p ∙ q ∙ r)
                      ( ∘-ap FmapL.f winl (σloop X x)
                      ∙ ap-∘ winl pinch (σloop X x)
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
              ∙ ap (ap winr) (! (Pinch.merid-β x))
              ∙ ∘-ap winr pinch (merid x)
              ∙ ap-∘ FmapR.f winr (merid x)) ⟩
        ap FmapR.f (ap winl (σloop X x)) ∙ ap FmapR.f wglue ∙ ap FmapR.f (ap winr (merid x))
          =⟨ ∙∙-ap FmapR.f (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
        ap FmapR.f (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
          =⟨ ! $ ap (ap FmapR.f) (Pinch.merid-β x) ⟩
        ap FmapR.f (ap pinch (merid x))
          =⟨ ∘-ap FmapR.f pinch (merid x) ⟩
        ap (FmapR.f ∘ pinch) (merid x)
          =∎
        where
          module Assoc = WedgeAssoc (⊙Susp X) (⊙Susp X) (⊙Susp X)
          module AssocInl = WedgeAssocInl (⊙Susp X) (⊙Susp X) (⊙Susp X)
          module FmapL = WedgeFmap ⊙pinch (⊙idf (⊙Susp X))
          module FmapR = WedgeFmap (⊙idf (⊙Susp X)) ⊙pinch

          lemma₀ : ∀ x → ap pinch (σloop X x)
            == ap winl (σloop X x) ∙ wglue ∙ ap winr (σloop X x) ∙ ! wglue
          lemma₀ x =
            ap pinch (σloop X x)
              =⟨ ap-∙ pinch (merid x) (! (merid (pt X))) ⟩
            ap pinch (merid x) ∙ ap pinch (! (merid (pt X)))
              =⟨ Pinch.merid-β x ∙2 (ap-! pinch (merid (pt X)) ∙ ap ! (Pinch.merid-β (pt X))) ⟩
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
           ⊙∨-fmap ⊙pinch (⊙idf (⊙Susp X)) ⊙∘ ⊙pinch
        ⊙∼ ⊙∨-fmap (⊙idf (⊙Susp X)) ⊙pinch ⊙∘ ⊙pinch
      ⊙assoc = assoc , idp

  Susp-cogroup-structure : CogroupStructure (⊙Susp X)
  Susp-cogroup-structure = record {
    co-h-struct = Susp-co-h-space-structure;
    ⊙inv = ⊙Susp-flip X;
    ⊙inv-l = ⊙inv-l;
    ⊙assoc = ⊙assoc}

  Susp⊙→-group-structure : ∀ {j} (Y : Ptd j) → GroupStructure (⊙Susp X ⊙→ Y)
  Susp⊙→-group-structure Y = cogroup⊙→-group-structure Susp-cogroup-structure Y

  Trunc-Susp⊙→-group : ∀ {j} (Y : Ptd j) → Group (lmax i j)
  Trunc-Susp⊙→-group Y = Trunc-group (Susp⊙→-group-structure Y)

module _ {i j} (X : Ptd i) where

  Lift-Susp-co-h-space-structure : CoHSpaceStructure (⊙Lift {j = j} (⊙Susp X))
  Lift-Susp-co-h-space-structure =
    Lift-co-h-space-structure {j = j} (Susp-co-h-space-structure X)

  Lift-Susp-cogroup-structure : CogroupStructure (⊙Lift {j = j} (⊙Susp X))
  Lift-Susp-cogroup-structure =
    Lift-cogroup-structure {j = j} (Susp-cogroup-structure X)

  LiftSusp⊙→-group-structure : ∀ {k} (Y : Ptd k) → GroupStructure (⊙Lift {j = j} (⊙Susp X) ⊙→ Y)
  LiftSusp⊙→-group-structure Y = cogroup⊙→-group-structure Lift-Susp-cogroup-structure Y

  Trunc-LiftSusp⊙→-group : ∀ {k} (Y : Ptd k) → Group (lmax (lmax i j) k)
  Trunc-LiftSusp⊙→-group Y = Trunc-group (LiftSusp⊙→-group-structure Y)
