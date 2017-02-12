{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.LoopSpaceCircle

-- This file is temporarily put in the cw/ directory for
-- development, but it actually belongs to somewhere else.

module homotopy.SphereEndomorphism where

  ⊙SphereS-endo-out : ∀ n
    → Trunc 0 (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))
    → Trunc 0 ( Sphere (S n)  →  Sphere (S n))
  ⊙SphereS-endo-out n = Trunc-rec Trunc-level ([_] ∘ fst)

  -- For [S¹], the pointedness is free because of the commutativity of its loop space.

  -- favonia: maybe one can simplify the proofs through
  --          an intermediate type [Σ S¹ (λ x → x == x)]?

  private
    ⊙S¹-endo-in'' : (base* : S¹) (loop* : base* == base*) → (⊙S¹ ⊙→ ⊙S¹)
    ⊙S¹-endo-in'' = S¹-elim
      (λ loop* → S¹-rec base loop* , idp)
      (↓-app→cst-in λ r → ap (λ loop* → (S¹-rec base loop* , idp)) (lemma₀ r)) where
      abstract
        lemma₀ : ∀ {loop₁ loop₂}
          → loop₁ == loop₂ [ (λ x → x == x) ↓ loop ]
          → loop₁ == loop₂
        lemma₀ {loop₁} {loop₂} p = anti-whisker-right loop $
          loop₁ ∙ loop
            =⟨ ↓-idf=idf-out' p ⟩
          loop ∙' loop₂
            =⟨ ∙'=∙ loop loop₂ ⟩
          loop ∙ loop₂
            =⟨ ΩS¹-is-abelian loop loop₂ ⟩
          loop₂ ∙ loop
            =∎

    ⊙S¹-endo-in' : (S¹ → S¹) → (⊙S¹ ⊙→ ⊙S¹)
    ⊙S¹-endo-in' f = ⊙S¹-endo-in'' (f base) (ap f loop)

  ⊙S¹-endo-in : Trunc 0 (S¹ → S¹) → Trunc 0 (⊙S¹ ⊙→ ⊙S¹)
  ⊙S¹-endo-in = Trunc-fmap ⊙S¹-endo-in'

  abstract
    ⊙S¹-endo-in-η : ∀ f → ⊙S¹-endo-in (⊙SphereS-endo-out 0 f) == f
    ⊙S¹-endo-in-η = Trunc-elim (λ _ → =-preserves-set Trunc-level)
      λ{(f , pt) → ap [_] $
        ⊙S¹-endo-in''-shifted pt (ap f loop) ∙ ⊙λ= (S¹-rec-η f) idp}
      where
      -- free one end to apply identification elimination
      ⊙S¹-endo-in''-shifted : {base* : S¹}
        (shift : base* == base) (loop* : base* == base*)
        → ⊙S¹-endo-in'' base* loop* == (S¹-rec base* loop* , shift)
      ⊙S¹-endo-in''-shifted idp _ = idp

    ⊙S¹-endo-out-β : ∀ f → ⊙SphereS-endo-out 0 (⊙S¹-endo-in f) == f
    ⊙S¹-endo-out-β = Trunc-elim (λ _ → =-preserves-level Trunc-level)
      λ f → ! (ap (λ f → [ fst (⊙S¹-endo-in' f) ]) (λ= $ S¹-rec-η f))
          ∙ ⊙S¹-endo-out'-β (f base) (ap f loop)
          ∙ ap [_] (λ= $ S¹-rec-η f)
      where
        -- free [base*] to apply circle elimination
        ⊙S¹-endo-out'-β : (base* : S¹) (loop* : base* == base*)
          →  [ fst (⊙S¹-endo-in' (S¹-rec base* loop*)) ]
          == [ S¹-rec base* loop* ] :> Trunc 0 (S¹ → S¹)
        ⊙S¹-endo-out'-β = S¹-elim
          (λ loop* → ap (λ loop* → [ S¹-rec base loop* ]) (S¹Rec.loop-β base loop*))
          (prop-has-all-paths-↓ $ Π-is-prop λ loop* → Trunc-level {n = 0} _ _)

  ⊙S¹-endo-out-is-equiv : is-equiv (⊙SphereS-endo-out 0)
  ⊙S¹-endo-out-is-equiv = is-eq _ ⊙S¹-endo-in ⊙S¹-endo-out-β ⊙S¹-endo-in-η

  -- For [Sphere (S (S n))], the pointedness is free because of its connectivity.

  private
    SphereSS-conn : ∀ n → is-connected 1 (Sphere (S (S n)))
    SphereSS-conn n = connected-≤T (≤T-+2+-l 1 (-2≤T ⟨ n ⟩₋₂)) (Sphere-conn (S (S n)))

    SphereSS-conn-path : ∀ n (x y : Sphere (S (S n))) → is-connected 0 (x == y)
    SphereSS-conn-path n x y = path-conn (SphereSS-conn n)

    SphereSS-has-all-trunc-paths : ∀ n (x y : Sphere (S (S n))) → Trunc 0 (x == y)
    SphereSS-has-all-trunc-paths n x y = –> (Trunc=-equiv [ x ] [ y ])
      (contr-has-all-paths (SphereSS-conn n) [ x ] [ y ])

  ⊙SphereSS-endo-in : ∀ n
    → Trunc 0 ( Sphere (S (S n))  →  Sphere (S (S n)))
    → Trunc 0 (⊙Sphere (S (S n)) ⊙→ ⊙Sphere (S (S n)))
  ⊙SphereSS-endo-in n = Trunc-rec Trunc-level λ f →
    Trunc-rec Trunc-level (λ pt → [ f , pt ])
      (SphereSS-has-all-trunc-paths n (f north) north)

  abstract
    ⊙SphereSS-endo-in-η : ∀ n f → ⊙SphereSS-endo-in n (⊙SphereS-endo-out (S n) f) == f
    ⊙SphereSS-endo-in-η n = Trunc-elim (λ _ → =-preserves-set Trunc-level)
      λ{(f , pt) → ap (Trunc-rec Trunc-level (λ pt → [ f , pt ]))
        (contr-has-all-paths (SphereSS-conn-path n (f north) north)
          (SphereSS-has-all-trunc-paths n (f north) north) [ pt ])}

    ⊙SphereSS-endo-out-β : ∀ n f → ⊙SphereS-endo-out (S n) (⊙SphereSS-endo-in n f) == f
    ⊙SphereSS-endo-out-β n = Trunc-elim (λ _ → =-preserves-set Trunc-level)
      λ f → Trunc-elim
        {P = λ pt → ⊙SphereS-endo-out (S n) (Trunc-rec Trunc-level (λ pt → [ f , pt ]) pt) == [ f ]}
        (λ _ → =-preserves-set Trunc-level)
        (λ pt → idp) (SphereSS-has-all-trunc-paths n (f north) north)

  ⊙SphereSS-endo-out-is-equiv : ∀ n → is-equiv (⊙SphereS-endo-out (S n))
  ⊙SphereSS-endo-out-is-equiv n = is-eq
    (⊙SphereS-endo-out (S n)) (⊙SphereSS-endo-in n)
    (⊙SphereSS-endo-out-β n) (⊙SphereSS-endo-in-η n)

  -- the unified interface

  ⊙SphereS-endo-out-is-equiv : ∀ n → is-equiv (⊙SphereS-endo-out n)
  ⊙SphereS-endo-out-is-equiv 0 = ⊙S¹-endo-out-is-equiv
  ⊙SphereS-endo-out-is-equiv (S n) = ⊙SphereSS-endo-out-is-equiv n

  ⊙SphereS-endo-in : ∀ n
    → Trunc 0 ( Sphere (S n)  →  Sphere (S n))
    → Trunc 0 (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))
  ⊙SphereS-endo-in n = is-equiv.g (⊙SphereS-endo-out-is-equiv n)
