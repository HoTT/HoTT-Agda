{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.LoopSpaceCircle
open import homotopy.PinSn

module homotopy.SphereEndomorphism where

  Sphere-endo : ∀ n → Type₀
  Sphere-endo n = Sphere n → Sphere n

  ⊙Sphere-endo : ∀ n → Type₀
  ⊙Sphere-endo n = ⊙Sphere n ⊙→ ⊙Sphere n

  ⊙LiftSphere-endo : ∀ {i} n → Type i
  ⊙LiftSphere-endo {i} n = ⊙Lift {j = i} (⊙Sphere n) ⊙→ ⊙Lift {j = i} (⊙Sphere n)

  Trunc-Sphere-endo : ∀ n → Type₀
  Trunc-Sphere-endo = Trunc 0 ∘ Sphere-endo

  Trunc-⊙Sphere-endo : ∀ n → Type₀
  Trunc-⊙Sphere-endo = Trunc 0 ∘ ⊙Sphere-endo

  Trunc-⊙LiftSphere-endo : ∀ {i} n → Type i
  Trunc-⊙LiftSphere-endo {i} = Trunc 0 ∘ ⊙LiftSphere-endo {i}

  {- Part 0: pointedness is free -}

  Trunc-⊙Sphere-endo-out : ∀ n
    → Trunc-⊙Sphere-endo n → Trunc-Sphere-endo n
  Trunc-⊙Sphere-endo-out n = Trunc-rec ([_] ∘ fst)

  -- For [S¹], the pointedness is free because of the commutativity of its loop space.

  -- favonia: maybe one can simplify the proofs through
  --          an intermediate type [Σ S¹ (λ x → x == x)]?

  private
    ⊙S¹-endo-in' : (base* : S¹) (loop* : base* == base*) → (⊙S¹ ⊙→ ⊙S¹)
    ⊙S¹-endo-in' = S¹-elim
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

    ⊙S¹-endo-in : (S¹ → S¹) → (⊙S¹ ⊙→ ⊙S¹)
    ⊙S¹-endo-in f = ⊙S¹-endo-in' (f base) (ap f loop)

  Trunc-⊙S¹-endo-in : Trunc 0 (S¹ → S¹) → Trunc 0 (⊙S¹ ⊙→ ⊙S¹)
  Trunc-⊙S¹-endo-in = Trunc-fmap ⊙S¹-endo-in

  abstract
    Trunc-⊙S¹-endo-in-η : ∀ f → Trunc-⊙S¹-endo-in (Trunc-⊙Sphere-endo-out 1 f) == f
    Trunc-⊙S¹-endo-in-η = Trunc-elim
      λ{(f , pt) → ap [_] $
        ⊙S¹-endo-in'-shifted pt (ap f loop) ∙ ⊙λ= (S¹-rec-η f , idp)}
      where
      -- free one end to apply identification elimination
      ⊙S¹-endo-in'-shifted : {base* : S¹}
        (shift : base* == base) (loop* : base* == base*)
        → ⊙S¹-endo-in' base* loop* == (S¹-rec base* loop* , shift)
      ⊙S¹-endo-in'-shifted idp _ = idp

    Trunc-⊙S¹-endo-out-β : ∀ f → Trunc-⊙Sphere-endo-out 1 (Trunc-⊙S¹-endo-in f) == f
    Trunc-⊙S¹-endo-out-β = Trunc-elim
      λ f → ! (ap (λ f → [ fst (⊙S¹-endo-in f) ]) (λ= $ S¹-rec-η f))
          ∙ ⊙S¹-endo-out-β (f base) (ap f loop)
          ∙ ap [_] (λ= $ S¹-rec-η f)
      where
        -- free [base*] to apply circle elimination
        ⊙S¹-endo-out-β : (base* : S¹) (loop* : base* == base*)
          →  [ fst (⊙S¹-endo-in (S¹-rec base* loop*)) ]
          == [ S¹-rec base* loop* ] :> Trunc 0 (S¹ → S¹)
        ⊙S¹-endo-out-β = S¹-elim
          (λ loop* → ap (λ loop* → [ S¹-rec base loop* ]) (S¹Rec.loop-β base loop*))
          prop-has-all-paths-↓

  Trunc-⊙S¹-endo-out-is-equiv : is-equiv (Trunc-⊙Sphere-endo-out 1)
  Trunc-⊙S¹-endo-out-is-equiv = is-eq _ Trunc-⊙S¹-endo-in Trunc-⊙S¹-endo-out-β Trunc-⊙S¹-endo-in-η

  -- For [Sphere (S (S n))], the pointedness is free because of its connectivity.

  private
    SphereSS-conn : ∀ n → is-connected 1 (Sphere (S (S n)))
    SphereSS-conn n = connected-≤T (≤T-+2+-l 1 (-2≤T ⟨ n ⟩₋₂))

    SphereSS-conn-path : ∀ n (x y : Sphere (S (S n))) → is-connected 0 (x == y)
    SphereSS-conn-path n x y = path-conn (SphereSS-conn n)

    SphereSS-has-all-trunc-paths : ∀ n (x y : Sphere (S (S n))) → Trunc 0 (x == y)
    SphereSS-has-all-trunc-paths n x y = –> (Trunc=-equiv [ x ] [ y ])
      (contr-has-all-paths {{SphereSS-conn n}} [ x ] [ y ])

  Trunc-⊙SphereSS-endo-in : ∀ n
    → Trunc-Sphere-endo (S (S n)) → Trunc-⊙Sphere-endo (S (S n))
  Trunc-⊙SphereSS-endo-in n = Trunc-rec λ f →
    Trunc-rec (λ pt → [ f , pt ])
      (SphereSS-has-all-trunc-paths n (f north) north)

  abstract
    Trunc-⊙SphereSS-endo-in-η : ∀ n f → Trunc-⊙SphereSS-endo-in n (Trunc-⊙Sphere-endo-out (S (S n)) f) == f
    Trunc-⊙SphereSS-endo-in-η n = Trunc-elim
      λ{(f , pt) → ap (Trunc-rec (λ pt → [ f , pt ]))
        (contr-has-all-paths {{SphereSS-conn-path n (f north) north}}
          (SphereSS-has-all-trunc-paths n (f north) north) [ pt ])}

    Trunc-⊙SphereSS-endo-out-β : ∀ n f → Trunc-⊙Sphere-endo-out (S (S n)) (Trunc-⊙SphereSS-endo-in n f) == f
    Trunc-⊙SphereSS-endo-out-β n = Trunc-elim
      λ f → Trunc-elim
        {P = λ pt → Trunc-⊙Sphere-endo-out (S (S n)) (Trunc-rec (λ pt → [ f , pt ]) pt) == [ f ]}
        (λ pt → idp) (SphereSS-has-all-trunc-paths n (f north) north)

  Trunc-⊙SphereSS-endo-out-is-equiv : ∀ n → is-equiv (Trunc-⊙Sphere-endo-out (S (S n)))
  Trunc-⊙SphereSS-endo-out-is-equiv n = is-eq
    (Trunc-⊙Sphere-endo-out (S (S n))) (Trunc-⊙SphereSS-endo-in n)
    (Trunc-⊙SphereSS-endo-out-β n) (Trunc-⊙SphereSS-endo-in-η n)

  -- the unified interface

  Trunc-⊙SphereS-endo-out-is-equiv : ∀ n → is-equiv (Trunc-⊙Sphere-endo-out (S n))
  Trunc-⊙SphereS-endo-out-is-equiv 0 = Trunc-⊙S¹-endo-out-is-equiv
  Trunc-⊙SphereS-endo-out-is-equiv (S n) = Trunc-⊙SphereSS-endo-out-is-equiv n

  Trunc-⊙SphereS-endo-in : ∀ n
    → Trunc-Sphere-endo (S n) → Trunc-⊙Sphere-endo (S n)
  Trunc-⊙SphereS-endo-in n = is-equiv.g (Trunc-⊙SphereS-endo-out-is-equiv n)

  {- Part 1: suspension is an isomorphism -}

  private
    open import homotopy.Freudenthal

    SSSSk≤SSk+2+SSk : ∀ k → S (S (S (S k))) ≤T S (S k) +2+ S (S k)
    SSSSk≤SSk+2+SSk k = ≤T-+2+-l 0 $ ≤T-+2+-r (S (S k)) $ -2≤T k

    SSn≤n+2+n : ∀ n → S (S ⟨ n ⟩) ≤T ⟨ n ⟩ +2+ ⟨ n ⟩
    SSn≤n+2+n n = SSSSk≤SSk+2+SSk ⟨ n ⟩₋₂

    module F n = FreudenthalEquiv
      ⟨ n ⟩₋₁ _ (SSn≤n+2+n n) (⊙Sphere (S (S n))) {{Sphere-conn (S (S n))}}

    import homotopy.TruncationLoopLadder as TLL
    import homotopy.SuspAdjointLoop as SAL
    import homotopy.SuspAdjointLoopLadder as SALL
    import homotopy.CircleHSpace as CHS
    import homotopy.Pi2HSusp as Pi2

    ⊙up : ∀ n → ⊙Sphere n ⊙→ ⊙Ω (⊙Sphere (S n))
    ⊙up n = SAL.η (⊙Sphere n)

    Ω^'S-Trunc-up-is-equiv : ∀ n → is-equiv (Ω^'-fmap (S n) (⊙Trunc-fmap {n = ⟨ S n ⟩} (⊙up (S n))))
    Ω^'S-Trunc-up-is-equiv O = snd (Ω-emap (Pi2.⊙eq⁻¹ CHS.⊙S¹-hSpace))
    Ω^'S-Trunc-up-is-equiv (S n) = snd (Ω^'-emap (S (S n)) (F.⊙eq n))

    Trunc-Ω^'S-up-is-equiv : ∀ n → is-equiv (Trunc-fmap {n = 0} (Ω^'-fmap (S n) (⊙up (S n))))
    Trunc-Ω^'S-up-is-equiv n = ⊙CommSquareEquiv-preserves-equiv (TLL.ladder (S n) (⊙up (S n))) (Ω^'S-Trunc-up-is-equiv n)

    Trunc-post⊙∘-Ω^'S-up-is-equiv : ∀ n →
      is-equiv (Trunc-fmap {n = 0} ((⊙Ω^'-fmap (S n) (⊙up (S n)) ⊙∘_) :> (_ → ⊙Bool ⊙→ _)))
    Trunc-post⊙∘-Ω^'S-up-is-equiv n = CommSquareEquiv-preserves'-equiv
      (Trunc-csemap (⊙Bool→-equiv-idf-nat (⊙Ω^'-fmap (S n) (⊙up (S n)))))
      (Trunc-Ω^'S-up-is-equiv n)

    Trunc-post⊙∘-upS-is-equiv : ∀ n →
      is-equiv (Trunc-fmap {n = 0} ((⊙up (S n) ⊙∘_) :> (_ → ⊙Sphere (S n) ⊙→ _)))
    Trunc-post⊙∘-upS-is-equiv n = CommSquareEquiv-preserves'-equiv
      (Trunc-csemap (SALL.ladder (S n) (⊙up (S n))))
      (Trunc-post⊙∘-Ω^'S-up-is-equiv n)

    final-fix : ∀ n →
      CommSquareEquiv
        (⊙Susp-fmap :> (⊙Sphere-endo (S n) → _))
        (SAL.η _ ⊙∘_)
        (idf _)
        (–> (SAL.eq _ _))
    final-fix n = comm-sqr (λ f → ! (SAL.η-natural f)) , idf-is-equiv _ , snd (SAL.eq _ _)

  Trunc-⊙SphereS-endo-Susp-is-equiv : ∀ n →
    is-equiv (Trunc-fmap ⊙Susp-fmap :> (Trunc-⊙Sphere-endo (S n) → _))
  Trunc-⊙SphereS-endo-Susp-is-equiv n =
    CommSquareEquiv-preserves'-equiv
      (Trunc-csemap (final-fix n))
      (Trunc-post⊙∘-upS-is-equiv n)
