{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.elims.CofPushoutSection

module homotopy.CofiberComp {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Z)) (g : fst (Y ⊙→ Z)) where

module CofiberComp where

  module H = ⊙WedgeRec f g
  ⊙h = H.⊙f; h = H.f

  module IntoCod = CofiberRec (fst f) {C = fst (⊙Cof ⊙h)}
    (cfbase _)
    (cfcod _)
    (λ x → cfglue _ (winl x))

  module Into = CofiberRec (fst (⊙cfcod f ⊙∘ g)) {C = fst (⊙Cof ⊙h)}
    (cfbase _)
    IntoCod.f
    (λ y → cfglue _ (winr y))

  into = Into.f

  out-glue : (w : X ∨ Y)
    → cfbase (fst (⊙cfcod f ⊙∘ g)) == cfcod _ (cfcod _ (h w))
  out-glue = Wedge-elim
    (λ x → (cfglue _ (snd Y)
            ∙ ! (ap (cfcod _ ∘ cfcod _) (snd f ∙ ! (snd g)))
            ∙ ! (ap (cfcod _) (cfglue _ (snd X))))
           ∙ ap (cfcod _) (cfglue _ x))
    (λ y → cfglue _ y)
    (↓-cst=app-from-square $
      out-square-lemma
        (cfglue _ (snd Y))
        (ap (cfcod _ ∘ cfcod _) (snd f ∙ ! (snd g)))
        (ap (cfcod _) (cfglue _ (snd X)))
      ⊡v∙ ! (ap-∘ (cfcod _ ∘ cfcod _) h wglue
             ∙ ap (ap (cfcod _ ∘ cfcod _)) H.glue-β))
    where
    out-square-lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : z == y) (r : w == z)
      → Square ((p ∙ ! q ∙ ! r) ∙ r) idp q p
    out-square-lemma idp idp idp = ids

  module Out = CofiberRec (fst ⊙h) {C = fst (⊙Cof (⊙cfcod f ⊙∘ g))}
    (cfbase _)
    (λ z → cfcod _ (cfcod _ z))
    out-glue

  out = Out.f

  into-out : ∀ c → into (out c) == c
  into-out = CofPushoutSection.elim h (λ _ → unit) (λ _ → idp)
    idp
    (λ _ → idp)
    (↓-∘=idf-in into out ∘ λ x →
      ap (ap into) (Out.glue-β (winl x))
      ∙ lemma₁ into
          (Into.glue-β (snd Y))
          (ap-! into (ap (cfcod _ ∘ cfcod _) (snd f ∙ ! (snd g)))
           ∙ ap ! (∘-ap into (cfcod _ ∘ cfcod _) (snd f ∙ ! (snd g)))
           ∙ ap (! ∘ ap (cfcod _)) (! H.glue-β)
           ∙ ap ! (∘-ap (cfcod _) h wglue))
          (ap-! into (ap (cfcod _) (cfglue _ (snd X)))
           ∙ ap ! (∘-ap into (cfcod _) (cfglue _ (snd X))
                   ∙ IntoCod.glue-β (snd X)))
          (∘-ap into (cfcod _) (cfglue _ x) ∙ IntoCod.glue-β x)
      ∙ ap (λ w → w ∙ cfglue _ (winl x)) (lemma₂ (cfglue _) wglue))
    (↓-∘=idf-in into out ∘ λ y →
      ap (ap into) (Out.glue-β (winr y))
      ∙ Into.glue-β y)
    where
    lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z u v : A}
      {p : x == y} {q : y == z} {r : z == u} {s : u == v}
      {p' : f x == f y} {q' : f y == f z} {r' : f z == f u} {s' : f u == f v}
      (α : ap f p == p') (β : ap f q == q')
      (γ : ap f r == r') (δ : ap f s == s')
      → ap f ((p ∙ q ∙ r) ∙ s) == (p' ∙ q' ∙ r') ∙ s'
    lemma₁ f {p = idp} {q = idp} {r = idp} {s = idp} idp idp idp idp = idp

    lemma₂ : ∀ {i j} {A : Type i} {B : Type j} {g : A → B} {b : B}
      (p : ∀ a → b == g a) {x y : A} (q : x == y)
      → p y ∙ ! (ap g q) ∙ ! (p x) == idp
    lemma₂ p {x} idp = !-inv-r (p x)

  out-into : ∀ κ → out (into κ) == κ
  out-into = Cofiber-elim _
    idp
    out-into-cod
    (↓-∘=idf-from-square out into ∘ vert-degen-square ∘ λ y →
      ap (ap out) (Into.glue-β y)
      ∙ Out.glue-β (winr y))
    where
    lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
      → Square p (p ∙ q) q idp
    lemma idp idp = ids

    out-into-cod : ∀ c → out (into (cfcod _ c)) == cfcod _ c
    out-into-cod = Cofiber-elim _
      (cfglue _ (snd Y)
       ∙ ! (ap (cfcod _ ∘ cfcod _) (snd f ∙ ! (snd g)))
       ∙ ! (ap (cfcod _) (cfglue _ (snd X))))
      (λ y → idp)
      (↓-='-from-square ∘ λ x →
        (ap-∘ out IntoCod.f (cfglue _ x)
         ∙ ap (ap out) (IntoCod.glue-β x)
         ∙ Out.glue-β (winl x))
        ∙v⊡ lemma _ _)

  eq : fst (⊙Cof (⊙cfcod f ⊙∘ g)) ≃ fst (⊙Cof ⊙h)
  eq = equiv into out into-out out-into

  ⊙path : ⊙Cof (⊙cfcod f ⊙∘ g) == ⊙Cof ⊙h
  ⊙path = ⊙ua (⊙ify-eq eq idp)
