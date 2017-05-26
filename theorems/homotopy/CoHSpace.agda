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
