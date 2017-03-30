{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
open import stash.modalities.FiberOfWedgeToProduct

module stash.modalities.ModalWedge {i} (M : Modality i)
  {A : Type i} {a₀ : A} {B : Type i} {b₀ : B} where

  open Modality M

  record args : Type (lsucc i) where
    field
      jn-conn : (a : A) (b : B) → is-◯-connected M ((a₀ == a) * (b₀ == b))
      R : A → B → ◯-Type M
      f : (a : A) → fst (R a b₀)
      g : (b : B) → fst (R a₀ b)
      p : f a₀ == g b₀

  module _ (r : args) where
    open args r

    private
      ⊙A = ⊙[ A , a₀ ]
      ⊙B = ⊙[ B , b₀ ]
      A⊙×B = ⊙A ⊙× ⊙B

    R' : de⊙ A⊙×B → ◯-Type M
    R' (a , b) = R a b

    ∨-to-×-is-◯-equiv : is-◯-equiv M (∨-to-× ⊙A ⊙B)
    ∨-to-×-is-◯-equiv (a , b) = transport! (is-◯-connected M) (ua (fiber-thm ⊙A ⊙B a b) ) (jn-conn a b)

    ext : (a : A) → (b : B) → fst (R a b)
    ext a b = ◯-extend M
      (∨-to-× ⊙A ⊙B)
      ∨-to-×-is-◯-equiv R'
      (Wedge-elim f g lemma)
      (a , b)

      where lemma : f (pt ⊙A) == g (pt ⊙B) [ (fst ∘ R') ∘ (∨-to-× ⊙A ⊙B) ↓ wglue ]
            lemma = ↓-ap-out (fst ∘ R') (∨-to-× ⊙A ⊙B) wglue
              (transport!
                (λ q → PathOver (fst ∘ R') q (f (pt ⊙A)) (g (pt ⊙B)))
                (∨-to-×-glue-β ⊙A ⊙B) p)



  
