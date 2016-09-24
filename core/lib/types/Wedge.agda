{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Span
open import lib.types.Unit

-- Wedge of two pointed types is defined as a particular case of pushout

module lib.types.Wedge where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  wedge-span : Span
  wedge-span = span (fst X) (fst Y) Unit (λ _ → snd X) (λ _ → snd Y)

  Wedge : Type (lmax i j)
  Wedge = Pushout wedge-span

  infix 80 _∨_
  _∨_ = Wedge

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  winl : fst X → X ∨ Y
  winl x = left x

  winr : fst Y → X ∨ Y
  winr y = right y

  wglue : winl (snd X) == winr (snd Y)
  wglue = glue tt

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙Wedge : Ptd (lmax i j)
  ⊙Wedge = ⊙[ Wedge X Y , winl (snd X) ]

  infix 80 _⊙∨_
  _⊙∨_ = ⊙Wedge

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙winl : X ⊙→ X ⊙∨ Y
  ⊙winl = (winl , idp)

  ⊙winr : Y ⊙→ X ⊙∨ Y
  ⊙winr = (winr , ! wglue)

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  module WedgeElim {k} {P : X ∨ Y → Type k}
    (inl* : (x : fst X) → P (winl x)) (inr* : (y : fst Y) → P (winr y))
    (glue* : inl* (snd X) == inr* (snd Y) [ P ↓ wglue ]) where

    private
      module M = PushoutElim inl* inr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  open WedgeElim public using () renaming (f to Wedge-elim)

  module WedgeRec {k} {C : Type k} (inl* : fst X → C) (inr* : fst Y → C)
    (glue* : inl* (snd X) == inr* (snd Y)) where

    private
      module M = PushoutRec {d = wedge-span X Y} inl* inr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  open WedgeRec public using () renaming (f to Wedge-rec)

module ⊙WedgeRec {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : X ⊙→ Z) (h : Y ⊙→ Z) where

  open WedgeRec (fst g) (fst h) (snd g ∙ ! (snd h)) public

  ⊙f : X ⊙∨ Y ⊙→ Z
  ⊙f = (f , snd g)

  ⊙winl-β : ⊙f ⊙∘ ⊙winl == g
  ⊙winl-β = idp

  ⊙winr-β : ⊙f ⊙∘ ⊙winr == h
  ⊙winr-β = ⊙λ= (λ _ → idp) $
    ap (_∙ snd g)
       (ap-! f wglue ∙ ap ! glue-β ∙ !-∙ (snd g) (! (snd h)))
    ∙ ∙-assoc (! (! (snd h))) (! (snd g)) (snd g)
    ∙ ap (! (! (snd h)) ∙_) (!-inv-l (snd g))
    ∙ ∙-unit-r (! (! (snd h)))
    ∙ !-! (snd h)

⊙Wedge-rec = ⊙WedgeRec.⊙f

⊙Wedge-rec-post∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (k : Z ⊙→ W) (g : X ⊙→ Z) (h : Y ⊙→ Z)
  → k ⊙∘ ⊙Wedge-rec g h == ⊙Wedge-rec (k ⊙∘ g) (k ⊙∘ h)
⊙Wedge-rec-post∘ k g h = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in $ ⊙WedgeRec.glue-β (k ⊙∘ g) (k ⊙∘ h)
               ∙ lemma (fst k) (snd g) (snd h) (snd k)
               ∙ ! (ap (ap (fst k)) (⊙WedgeRec.glue-β g h))
               ∙ ∘-ap (fst k) (fst (⊙Wedge-rec g h)) wglue))
  idp
  where
  lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} {w : B}
    (p : x == z) (q : y == z) (r : f z == w)
    → (ap f p ∙ r) ∙ ! (ap f q ∙ r) == ap f (p ∙ ! q)
  lemma f idp idp idp = idp

⊙Wedge-rec-η : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Wedge-rec ⊙winl ⊙winr == ⊙idf (X ⊙∨ Y)
⊙Wedge-rec-η = ⊙λ=
  (Wedge-elim (λ _ → idp) (λ _ → idp)
    (↓-='-in $ ap-idf wglue
               ∙ ! (!-! wglue)
               ∙ ! (⊙WedgeRec.glue-β ⊙winl ⊙winr)))
  idp

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  add-wglue : fst (X ⊙⊔ Y) → X ∨ Y
  add-wglue (inl x) = winl x
  add-wglue (inr y) = winr y

  ⊙add-wglue : X ⊙⊔ Y ⊙→ X ⊙∨ Y
  ⊙add-wglue = add-wglue , idp

module Fold {i} {X : Ptd i} = ⊙WedgeRec (⊙idf X) (⊙idf X)
fold = Fold.f
⊙fold = Fold.⊙f

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  module Projl = ⊙WedgeRec (⊙idf X) (⊙cst {X = Y})
  module Projr = ⊙WedgeRec (⊙cst {X = X}) (⊙idf Y)

  projl = Projl.f
  projr = Projr.f
  ⊙projl = Projl.⊙f
  ⊙projr = Projr.⊙f

module _ where

  private
    module WedgeFMap {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
      (F : X ⊙→ X') (G : Y ⊙→ Y')
      = WedgeRec {C = X' ∨ Y'} (winl ∘ fst F) (winr ∘ fst G)
        (ap winl (snd F) ∙ (wglue ∙' ! (ap winr (snd G))))

  ∨-fmap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
    → X ⊙→ X' → Y ⊙→ Y' → (X ∨ Y → X' ∨ Y')
  ∨-fmap = WedgeFMap.f

  -- XXX Needs some clean-ups.
  ∨-emap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
    → X ⊙≃ X' → Y ⊙≃ Y' → X ∨ Y ≃ X' ∨ Y'
  ∨-emap {i} {i'} {j} {j'} {X} {X'} {Y} {Y'} ⊙eqX ⊙eqY =
    equiv (to ⊙eqX ⊙eqY) (from ⊙eqX ⊙eqY) (to-from ⊙eqX ⊙eqY) (from-to ⊙eqX ⊙eqY) where
      to = λ {X' : Ptd i'} {Y' : Ptd j'} (⊙eqX : X ⊙≃ X') (⊙eqY : Y ⊙≃ Y')
        → ∨-fmap (⊙–> ⊙eqX) (⊙–> ⊙eqY)
      from = λ {X' : Ptd i'} {Y' : Ptd j'} (⊙eqX : X ⊙≃ X') (⊙eqY : Y ⊙≃ Y')
        → ∨-fmap (⊙<– ⊙eqX) (⊙<– ⊙eqY)

      path-lemma₀ : ∀ {i j} {A : Type i} {B : Type j}
        (f : A → B) {a₁ a₂ a₃ a₄ : A} {b₅ : B}
        (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (p₃ : a₄ == a₃) (p₄ : f a₄ == b₅)
        → ap f (p₁ ∙ p₂ ∙' ! p₃) ∙ p₄ == ap f p₁ ∙' ap f p₂ ∙' ! (ap f p₃) ∙ p₄
      path-lemma₀ f idp idp idp idp = idp

      path-lemma₀' : ∀ {i} {A : Type i} {a₁ a₂ a₃ a₄ : A}
        (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (p₃ : a₄ == a₃)
        → (p₁ ∙ p₂ ∙' ! p₃) ∙ p₃ == p₁ ∙' p₂
      path-lemma₀' idp idp idp = idp

      to-from : ∀ {X'} {Y'} (⊙eqX : X ⊙≃ X') (⊙eqY : Y ⊙≃ Y')
        → ∀ b → to ⊙eqX ⊙eqY (from ⊙eqX ⊙eqY b) == b
      to-from ((Xf , idp) , Xf-ise) ((Yf , idp) , Yf-ise) = Wedge-elim
        (ap winl ∘ Xf.f-g) (ap winr ∘ Yf.f-g)
        (↓-app=idf-in $
            ap winl (Xf.f-g (Xf (snd X))) ∙' wglue
              =⟨ ap2 _∙'_ (! path-lemma₁) (! To.glue-β) ⟩
            ap to' (ap winl (Xf.g-f (snd X))) ∙' ap to' wglue
              =⟨ ! $ !-inv-l (ap to' (ap winr (Yf.g-f (snd Y))))
                |in-ctx (λ p →
                  ap to' (ap winl (Xf.g-f (snd X)))
                  ∙' ap to' wglue
                  ∙' p) ⟩
            ap to' (ap winl (Xf.g-f (snd X)))
            ∙' ap to' wglue
            ∙' ! ( ap to' (ap winr (Yf.g-f (snd Y))))
            ∙ ap to' (ap winr (Yf.g-f (snd Y)))
              =⟨ path-lemma₂
                |in-ctx (λ p →
                  ap to' (ap winl (Xf.g-f (snd X)))
                  ∙' ap to' wglue
                  ∙' ! (ap to' (ap winr (Yf.g-f (snd Y))))
                  ∙ p) ⟩
            ap to' (ap winl (Xf.g-f (snd X)))
            ∙' ap to' wglue
            ∙' ! ( ap to' (ap winr (Yf.g-f (snd Y))))
            ∙ ap winr (Yf.f-g (Yf (snd Y)))
              =⟨ ! $ path-lemma₀ to'
                    (ap winl (Xf.g-f (snd X)))
                    wglue
                    (ap winr (Yf.g-f (snd Y)))
                    (ap winr (Yf.f-g (Yf (snd Y)))) ⟩
            ap to' ( ap winl (Xf.g-f (snd X))
                   ∙ wglue
                   ∙' ! (ap winr (Yf.g-f (snd Y))))
            ∙ ap winr (Yf.f-g (Yf (snd Y)))
              =⟨ ! From.glue-β |in-ctx ap to' |in-ctx _∙ ap winr (Yf.f-g (Yf (snd Y))) ⟩
            ap to' (ap from' wglue) ∙ ap winr (Yf.f-g (Yf (snd Y)))
              =⟨ ∘-ap to' from' wglue |in-ctx _∙ ap winr (Yf.f-g (Yf (snd Y))) ⟩
            ap (to' ∘ from') wglue ∙ ap winr (Yf.f-g (Yf (snd Y)))
              =∎)
        where
          module Xf = is-equiv Xf-ise
          module Yf = is-equiv Yf-ise
          module To = WedgeFMap (Xf , idp) (Yf , idp)
          module From = WedgeFMap (Xf.g , Xf.g-f (snd X)) (Yf.g , Yf.g-f (snd Y))
          to' = To.f
          from' = From.f

          path-lemma₁ : ap to' (ap winl (Xf.g-f (snd X)))
                     == ap winl (Xf.f-g (Xf (snd X)))
          path-lemma₁ = ∘-ap to' winl (Xf.g-f (snd X))
                      ∙ ap-∘ winl Xf (Xf.g-f (snd X))
                      ∙ ap (ap winl) (Xf.adj (snd X))

          path-lemma₂ : ap to' (ap winr (Yf.g-f (snd Y)))
                     == ap winr (Yf.f-g (Yf (snd Y)))
          path-lemma₂ = ∘-ap to' winr (Yf.g-f (snd Y))
                      ∙ ap-∘ winr Yf (Yf.g-f (snd Y))
                      ∙ ap (ap winr) (Yf.adj (snd Y))

      from-to : ∀ {X'} {Y'} (⊙eqX : X ⊙≃ X') (⊙eqY : Y ⊙≃ Y')
        → ∀ a → from ⊙eqX ⊙eqY (to ⊙eqX ⊙eqY a) == a
      from-to ((Xf , idp) , Xf-ise) ((Yf , idp) , Yf-ise) = Wedge-elim
        (ap winl ∘ Xf.g-f) (ap winr ∘ Yf.g-f)
        (↓-app=idf-in $
            ap winl (Xf.g-f (snd X)) ∙' wglue
              =⟨ ! $ path-lemma₀'
                  (ap winl (Xf.g-f (snd X)))
                  wglue
                  (ap winr (Yf.g-f (snd Y))) ⟩
            ( ap winl (Xf.g-f (snd X))
              ∙ wglue
              ∙' ! (ap winr (Yf.g-f (snd Y))))
            ∙ ap winr (Yf.g-f (snd Y))
              =⟨ ! From.glue-β |in-ctx _∙ ap winr (Yf.g-f (snd Y)) ⟩
            ap from' wglue ∙ ap winr (Yf.g-f (snd Y))
              =⟨ ! To.glue-β |in-ctx ap from' |in-ctx _∙ ap winr (Yf.g-f (snd Y)) ⟩
            ap from' (ap to' wglue) ∙ ap winr (Yf.g-f (snd Y))
              =⟨ ∘-ap from' to' wglue |in-ctx _∙ ap winr (Yf.g-f (snd Y)) ⟩
            ap (from' ∘ to') wglue ∙ ap winr (Yf.g-f (snd Y))
              =∎)
        where
          module Xf = is-equiv Xf-ise
          module Yf = is-equiv Yf-ise
          module To = WedgeFMap (Xf , idp) (Yf , idp)
          module From = WedgeFMap (Xf.g , Xf.g-f (snd X)) (Yf.g , Yf.g-f (snd Y))
          to' = To.f
          from' = From.f

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'} where

  private
    module ⊙WedgeFMap (F : X ⊙→ X') (G : Y ⊙→ Y')
      = ⊙WedgeRec {Z = X' ⊙∨ Y'} (winl ∘ fst F , ap winl (snd F)) (winr ∘ fst G , ! (wglue ∙' ! (ap winr (snd G))))

  ⊙∨-fmap : X ⊙→ X' → Y ⊙→ Y' → X ⊙∨ Y ⊙→ X' ⊙∨ Y'
  ⊙∨-fmap = ⊙WedgeFMap.⊙f

  ⊙∨-emap : X ⊙≃ X' → Y ⊙≃ Y' → X ⊙∨ Y ⊙≃ X' ⊙∨ Y'
  ⊙∨-emap ⊙eqX ⊙eqY = ⊙∨-fmap (⊙–> ⊙eqX) (⊙–> ⊙eqY) ,
    transport
      (λ p → is-equiv (Wedge-rec {C = X' ∨ Y'}
        (winl ∘ fst (⊙–> ⊙eqX)) (winr ∘ fst (⊙–> ⊙eqY)) (ap winl (snd (⊙–> ⊙eqX)) ∙ p)))
      (! $ !-! (wglue ∙' ! (ap winr (snd (⊙–> ⊙eqY)))))
      (snd (∨-emap ⊙eqX ⊙eqY))
