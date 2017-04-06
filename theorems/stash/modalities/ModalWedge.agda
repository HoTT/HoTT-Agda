{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities

module stash.modalities.ModalWedge {i} (M : Modality i)
  {A : Type i} {a₀ : A} {B : Type i} {b₀ : B} where

  open Modality M
  private
    ⊙A = ⊙[ A , a₀ ]
    ⊙B = ⊙[ B , b₀ ]
    A⊙×B = ⊙A ⊙× ⊙B
  open import stash.modalities.FiberOfWedgeToProduct ⊙A ⊙B

  record args : Type (lsucc i) where
    field
      jn-conn : (a : A) (b : B) → is-◯-connected ((a₀ == a) * (b₀ == b))
      R : A → B → ◯-Type
      f : (a : A) → fst (R a b₀)
      g : (b : B) → fst (R a₀ b)
      p : f a₀ == g b₀

  module _ (r : args) where
    open args r

    abstract
      ∨-to-×-is-◯-equiv : is-◯-equiv ∨-to-×
      ∨-to-×-is-◯-equiv (a , b) = equiv-preserves-◯-conn (fiber-thm a b ⁻¹) (jn-conn a b)

    module A∨BToR = WedgeElim f g
      (↓-ap-out= (fst ∘ uncurry R) ∨-to-× wglue ∨-to-×-glue-β p)

    A∨B-to-R : ∀ w → fst (uncurry R (∨-to-× w))
    A∨B-to-R = A∨BToR.f

    ext : (a : A) → (b : B) → fst (R a b)
    ext = curry $ ◯-extend ∨-to-×-is-◯-equiv (uncurry R) A∨B-to-R

  module _ {r : args} where
    open args r

    abstract
      β-l : (a : A) → ext r a b₀ == f a
      β-l a = ◯-extend-β (∨-to-×-is-◯-equiv r) (uncurry R) (A∨B-to-R r) (winl a)

      β-r : (b : B) → ext r a₀ b == g b
      β-r b = ◯-extend-β (∨-to-×-is-◯-equiv r) (uncurry R) (A∨B-to-R r) (winr b)

      coh : ! (β-l a₀) ∙ β-r b₀ == p
      coh = ap (! (β-l a₀) ∙_) (! (∙'-unit-l (β-r b₀)) ∙ ! lemma₁)
          ∙ ! (∙-assoc (! (β-l a₀)) (β-l a₀) p)
          ∙ ap (_∙ p) (!-inv-l (β-l a₀))
        where
          -- maybe this has been proved somewhere?
          lemma₀ : ∀ {i j k} {A : Type i} {B : Type j} (C : (b : B) → Type k)
            (f : A → B) {x y} (p : x == y) {q : f x == f y} (r : ap f p == q)
            {cx cx' : C (f x)} {cy cy' : C (f y)}
            (s : cx' == cy' [ C ↓ q ]) (t : cx == cy [ C ↓ q ])
            (u : cx == cx') (v : cy == cy')
            → u ◃ ↓-ap-out= C f p r s == ↓-ap-out= C f p r t ▹ v
            → u ◃ s == t ▹ v
          lemma₀ C f idp idp idp idp u v u=v = u=v

          lemma₁ : β-l a₀ ∙ p == idp ∙' β-r b₀
          lemma₁ = lemma₀ (fst ∘ uncurry R) ∨-to-× wglue ∨-to-×-glue-β
            p idp (β-l a₀) (β-r b₀)
            ( ap (β-l a₀ ◃_) (! (A∨BToR.glue-β r))
            ∙ ↓-=-out (apd (◯-extend-β (∨-to-×-is-◯-equiv r) (uncurry R) (A∨B-to-R r)) wglue)
            ∙ ap (_▹ β-r b₀)
                (apd-∘'' (◯-extend (∨-to-×-is-◯-equiv r) (uncurry R) (A∨B-to-R r))
                   ∨-to-× wglue ∨-to-×-glue-β))
