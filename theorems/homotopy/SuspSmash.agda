{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.SuspSmash
open import homotopy.elims.CofPushoutSection

-- Σ(X∧Y) ≃ X * Y

module homotopy.SuspSmash {i j} (X : Ptd i) (Y : Ptd j) where

private

  {- path lemmas -}
  private
    reduce-x : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : z == y)
      → p ∙ ! q ∙ q ∙ ! p ∙ p == p
    reduce-x idp idp = idp

    reduce-y : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : x == z)
      → p ∙ ! p ∙ q ∙ ! q ∙ p == p
    reduce-y idp idp = idp

  module Into = SuspRec {A = Smash X Y}
    {C = de⊙ X * de⊙ Y}
    (left (pt X))
    (right (pt Y))
    (Smash-rec
      (λ x y →
        jglue (pt X) (pt Y) ∙ ! (jglue x (pt Y))
        ∙ jglue x y
        ∙ ! (jglue (pt X) y) ∙ jglue (pt X) (pt Y))
      (jglue (pt X) (pt Y))
      (jglue (pt X) (pt Y))
      (λ x → reduce-x (jglue (pt X) (pt Y)) (jglue x (pt Y)))
      (λ y → reduce-y (jglue (pt X) (pt Y)) (jglue (pt X) y)))

  into = Into.f

  module Out = JoinRec
    {C = Susp (Smash X Y)}
    (λ _ → north)
    (λ _ → south)
    (λ x y → merid (smin x y))

  out = Out.f

  abstract
    into-out : (j : de⊙ X * de⊙ Y) → into (out j) == j
    into-out = Join-elim
      (λ x → glue (pt X , pt Y) ∙ ! (glue (x , pt Y)))
      (λ y → ! (glue (pt X , pt Y)) ∙ glue (pt X , y))
      (λ x y → ↓-∘=idf-from-square into out $
        (ap (ap into) (Out.glue-β x y)
         ∙ Into.merid-β (smin x y))
        ∙v⊡ lemma (glue (pt X , pt Y)) (glue (x , pt Y))
                  (glue (pt X , y)) (glue (x , y)))
      where
      lemma : ∀ {i} {A : Type i} {x y z w : A}
        (p : x == y) (q : z == y) (r : x == w) (s : z == w)
        → Square (p ∙ ! q) (p ∙ ! q ∙ s ∙ ! r ∙ p) s (! p ∙ r)
      lemma idp idp idp s =
        vert-degen-square (∙-unit-r s)

    out-into : (σ : Susp (Smash X Y)) → out (into σ) == σ
    out-into = SuspSmash-elim
      idp
      idp
      (λ x y → ↓-∘=idf-in' out into $
        ap (ap out) (Into.merid-β (smin x y))
        ∙ lemma₁ out (Out.glue-β (pt X) (pt Y))
                     (Out.glue-β x (pt Y))
                     (Out.glue-β x y)
                     (Out.glue-β (pt X) y)
                     (Out.glue-β (pt X) (pt Y))
        ∙ lemma₂ {p = merid (smin (pt X) (pt Y))}
                 {q = merid (smin x (pt Y))}
                 {r = merid (smin x y)}
                 {s = merid (smin (pt X) y)}
                 {t = merid (smin (pt X) (pt Y))}
            (ap merid (smgluel (pt X) ∙ ! (smgluel x)))
            (ap merid (smgluer y ∙ ! (smgluer (pt Y)))))
      where
      lemma₁ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
        {x y z u v w : A}
        {p : x == y} {q : z == y} {r : z == u} {s : v == u} {t : v == w}
        {p' : f x == f y} {q' : f z == f y} {r' : f z == f u}
        {s' : f v == f u} {t' : f v == f w}
        (α : ap f p == p') (β : ap f q == q') (γ : ap f r == r')
        (δ : ap f s == s') (ε : ap f t == t')
        → ap f (p ∙ ! q ∙ r ∙ ! s ∙ t) == p' ∙ ! q' ∙ r' ∙ ! s' ∙ t'
      lemma₁ f {p = idp} {q = idp} {r = idp} {s = idp} {t = idp}
            idp idp idp idp idp
        = idp

      lemma₂ : ∀ {i} {A : Type i} {x y z u : A}
        {p q : x == y} {r : x == z} {s t : u == z}
        (α : p == q) (β : s == t)
        → p ∙ ! q  ∙ r ∙ ! s ∙ t == r
      lemma₂ {p = idp} {r = idp} {s = idp} idp idp = idp

module SuspSmash where

  eq : Susp (Smash X Y) ≃ (de⊙ X * de⊙ Y)
  eq = equiv into out into-out out-into

  ⊙eq : ⊙Susp (X ∧ Y) ⊙≃ (X ⊙* Y)
  ⊙eq = ≃-to-⊙≃ eq idp
