{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.elims.CofPushoutSection

module homotopy.CofiberComp {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Z) (g : Y ⊙→ Z) where

module CofiberComp where

  module H = ⊙WedgeRec f g
  ⊙h = H.⊙f; h = H.f

  module IntoCod = CofiberRec {f = fst f} {C = fst (⊙Cofiber ⊙h)}
    cfbase
    cfcod
    (λ x → cfglue (winl x))

  module Into = CofiberRec {f = fst (⊙cfcod' f ⊙∘ g)} {C = fst (⊙Cofiber ⊙h)}
    cfbase
    IntoCod.f
    (λ y → cfglue (winr y))

  into = Into.f

  out-glue : (w : X ∨ Y)
    → cfbase' (fst (⊙cfcod' f ⊙∘ g)) == cfcod (cfcod (h w))
  out-glue = Wedge-elim
    (λ x → (cfglue (snd Y)
            ∙ ! (ap (cfcod ∘ cfcod) (snd f ∙ ! (snd g)))
            ∙ ! (ap cfcod (cfglue (snd X))))
           ∙ ap cfcod (cfglue x))
    cfglue
    (↓-cst=app-from-square $
      out-square-lemma
        (cfglue (snd Y))
        (ap (cfcod ∘ cfcod) (snd f ∙ ! (snd g)))
        (ap cfcod (cfglue (snd X)))
      ⊡v∙ ! (ap-∘ (cfcod ∘ cfcod) h wglue
             ∙ ap (ap (cfcod ∘ cfcod)) H.glue-β))
    where
    out-square-lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : z == y) (r : w == z)
      → Square ((p ∙ ! q ∙ ! r) ∙ r) idp q p
    out-square-lemma idp idp idp = ids

  module Out = CofiberRec {C = fst (⊙Cofiber (⊙cfcod' f ⊙∘ g))}
    cfbase
    (λ z → cfcod (cfcod z))
    out-glue

  out = Out.f

  into-out : ∀ c → into (out c) == c
  into-out = CofPushoutSection.elim {h = h} (λ _ → unit) (λ _ → idp)
    idp
    (λ _ → idp)
    (↓-∘=idf-in into out ∘ λ x →
      ap (ap into) (Out.glue-β (winl x))
      ∙ lemma₁ into
          (Into.glue-β (snd Y))
          (ap-! into (ap (cfcod ∘ cfcod) (snd f ∙ ! (snd g)))
           ∙ ap ! (∘-ap into (cfcod ∘ cfcod) (snd f ∙ ! (snd g)))
           ∙ ap (! ∘ ap cfcod) (! H.glue-β)
           ∙ ap ! (∘-ap cfcod h wglue))
          (ap-! into (ap cfcod (cfglue (snd X)))
           ∙ ap ! (∘-ap into cfcod (cfglue (snd X))
                   ∙ IntoCod.glue-β (snd X)))
          (∘-ap into cfcod (cfglue x) ∙ IntoCod.glue-β x)
      ∙ ap (λ w → w ∙ cfglue (winl x)) (lemma₂ cfglue wglue))
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
  out-into = Cofiber-elim
    idp
    out-into-cod
    (↓-∘=idf-from-square out into ∘ vert-degen-square ∘ λ y →
      ap (ap out) (Into.glue-β y)
      ∙ Out.glue-β (winr y))
    where
    lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
      → Square p (p ∙ q) q idp
    lemma idp idp = ids

    out-into-cod : ∀ c → out (into (cfcod c)) == cfcod c
    out-into-cod = Cofiber-elim
      (cfglue (snd Y)
       ∙ ! (ap (cfcod ∘ cfcod) (snd f ∙ ! (snd g)))
       ∙ ! (ap cfcod (cfglue (snd X))))
      (λ y → idp)
      (↓-='-from-square ∘ λ x →
        (ap-∘ out IntoCod.f (cfglue x)
         ∙ ap (ap out) (IntoCod.glue-β x)
         ∙ Out.glue-β (winl x))
        ∙v⊡ lemma _ _)

  eq : fst (⊙Cofiber (⊙cfcod' f ⊙∘ g)) ≃ fst (⊙Cofiber ⊙h)
  eq = equiv into out into-out out-into

  ⊙eq : ⊙Cofiber (⊙cfcod' f ⊙∘ g) ⊙≃ ⊙Cofiber ⊙h
  ⊙eq = ≃-to-⊙≃ eq idp
