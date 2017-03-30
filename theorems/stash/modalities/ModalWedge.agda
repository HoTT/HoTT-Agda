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
    ∨-to-×-is-◯-equiv (a , b) = equiv-preserves-level (◯-thm ⁻¹) (jn-conn a b)

      where thm : hfiber (∨-to-× ⊙A ⊙B) (a , b) ≃ (pt ⊙A == a) * (pt ⊙B == b)
            thm = fiber-thm ⊙A ⊙B a b

            ◯-thm : ◯ (hfiber (∨-to-× ⊙A ⊙B) (a , b)) ≃ ◯ ((a₀ == a) * (b₀ == b))
            ◯-thm = ◯-func M (fst thm) , ◯-func-is-equiv M (fst thm) (snd thm)

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



  
