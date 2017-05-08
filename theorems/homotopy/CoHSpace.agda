{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.CoHSpace where

record CoHSpaceStructure {i} (X : Ptd i) : Type i where
  constructor coHSpaceStructure
  field
    coμ : X ⊙→ X ⊙∨ X
    ∨-to-×-coμ-is-Δ : ∀ x → ∨-to-× (fst coμ x) == (x , x)

module _ {i} (X : Ptd i) where
  private
    A = de⊙ X
    e = pt X

  module Pinch = SuspRec (winl north) (winr south)
    (λ a → ap winl (σloop X a) ∙ wglue ∙' ap winr (merid a))

  pinch : Susp A → ⊙Susp X ∨ ⊙Susp X
  pinch = Pinch.f

  ⊙pinch : ⊙Susp X ⊙→ ⊙Susp X ⊙∨ ⊙Susp X
  ⊙pinch = pinch , idp

  fst-⊙pinch-to-× : ∀ x → fst (∨-to-× (pinch x)) == x
  fst-⊙pinch-to-× = Susp-elim idp (merid e) λ x → ↓-∘=idf-in' (fst ∘ ∨-to-×) pinch $
    ap (fst ∘ ∨-to-×) (ap pinch (merid x)) ∙' merid e
      =⟨ ap (_∙' merid e) $
        ap (fst ∘ ∨-to-×) (ap pinch (merid x))
          =⟨ ap (ap (fst ∘ ∨-to-×)) $ Pinch.merid-β x ⟩
        ap (fst ∘ ∨-to-×) (ap winl (σloop X x) ∙ wglue ∙' ap winr (merid x))
          =⟨ ap-∙ (fst ∘ ∨-to-×) (ap winl (σloop X x)) (wglue ∙' ap winr (merid x)) ⟩
        ap (fst ∘ ∨-to-×) (ap winl (σloop X x))
        ∙ ap (fst ∘ ∨-to-×) (wglue ∙' ap winr (merid x))
          =⟨ ap2 _∙_ (∘-ap (fst ∘ ∨-to-×) winl (σloop X x)) (ap-∙' (fst ∘ ∨-to-×) wglue (ap winr (merid x))) ⟩
        ap (idf _) (σloop X x)
        ∙ ap (fst ∘ ∨-to-×) wglue
        ∙' ap (fst ∘ ∨-to-×) (ap winr (merid x))
          =⟨ ap2 _∙_ (ap-idf (σloop X x)) (ap2 _∙'_ (ap-∘ fst (∨-to-×) wglue)  (∘-ap (fst ∘ ∨-to-×) winr (merid x))) ⟩
        σloop X x
        ∙ ap fst (ap ∨-to-× wglue)
        ∙' ap (cst north) (merid x)
          =⟨ ap (λ p → σloop X x ∙ p) $ ap2 _∙'_ (ap (ap fst) ∨-to-×-glue-β) (ap-cst north (merid x)) ⟩
        σloop X x ∙ idp
          =⟨ ∙-unit-r (σloop X x) ⟩
        σloop X x
          =∎ ⟩
    σloop X x ∙' merid e
      =⟨ ap (λ p → p ∙' merid e) (∙=∙' (merid x) (! (merid e))) ∙ ∙'-assoc (merid x) (! (merid e)) (merid e) ⟩
    merid x ∙' ! (merid e) ∙' merid e
      =⟨ ap (merid x ∙'_) (!-inv'-l (merid e)) ⟩
    merid x
      =∎

  snd-⊙pinch-to-× : ∀ x → snd (∨-to-× (pinch x)) == x
  snd-⊙pinch-to-× = Susp-elim idp idp λ x → ↓-∘=idf-in' (snd ∘ ∨-to-×) pinch $
    ap (snd ∘ ∨-to-×) (ap pinch (merid x))
      =⟨ ap (ap (snd ∘ ∨-to-×)) $ Pinch.merid-β x ⟩
    ap (snd ∘ ∨-to-×) (ap winl (σloop X x) ∙ wglue ∙' ap winr (merid x))
      =⟨ ap-∙ (snd ∘ ∨-to-×) (ap winl (σloop X x)) (wglue ∙' ap winr (merid x)) ⟩
    ap (snd ∘ ∨-to-×) (ap winl (σloop X x))
    ∙ ap (snd ∘ ∨-to-×) (wglue ∙' ap winr (merid x))
      =⟨ ap2 _∙_ (∘-ap (snd ∘ ∨-to-×) winl (σloop X x)) (ap-∙' (snd ∘ ∨-to-×) wglue (ap winr (merid x))) ⟩
    ap (cst north) (σloop X x)
    ∙ ap (snd ∘ ∨-to-×) wglue
    ∙' ap (snd ∘ ∨-to-×) (ap winr (merid x))
      =⟨ ap2 _∙_ (ap-cst north (σloop X x)) (ap2 _∙'_ (ap-∘ snd ∨-to-× wglue)  (∘-ap (snd ∘ ∨-to-×) winr (merid x))) ⟩
    ap snd (ap ∨-to-× wglue)
    ∙' ap (idf _) (merid x)
      =⟨ ap2 _∙'_ (ap (ap snd) ∨-to-×-glue-β) (ap-idf (merid x)) ⟩
    idp ∙' merid x
      =⟨ ∙'-unit-l (merid x) ⟩
    merid x
      =∎

  Susp-co-h-space-structure : CoHSpaceStructure (⊙Susp X)
  Susp-co-h-space-structure = record {
    coμ = ⊙pinch;
    ∨-to-×-coμ-is-Δ = λ x → pair×= (fst-⊙pinch-to-× x) (snd-⊙pinch-to-× x)}
