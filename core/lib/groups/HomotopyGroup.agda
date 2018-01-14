{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Group
open import lib.types.LoopSpace
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.groups.GroupProduct
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism
open import lib.groups.LoopSpace
open import lib.groups.TruncationGroup
open import lib.groups.Unit

module lib.groups.HomotopyGroup where

{- Higher homotopy groups -}
module _ {i} where

  πS : (n : ℕ) (X : Ptd i) → Group i
  πS n X = Trunc-group (Ω^S-group-structure n X)

  π'S : (n : ℕ) (X : Ptd i) → Group i
  π'S n X = Trunc-group (Ω^'S-group-structure n X)

  fundamental-group : (X : Ptd i) → Group i
  fundamental-group X = πS 0 X

module _ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} where

  πS-fmap : X ⊙→ Y → (πS n X →ᴳ πS n Y)
  πS-fmap F = Trunc-group-fmap (Ω^S-group-structure-fmap n F)

  π'S-fmap : X ⊙→ Y → (π'S n X →ᴳ π'S n Y)
  π'S-fmap F = Trunc-group-fmap (Ω^'S-group-structure-fmap n F)

  πS-emap : (X ⊙≃ Y) → (πS n X ≃ᴳ πS n Y)
  πS-emap e = Trunc-group-emap (Ω^S-group-structure-emap n e)

  π'S-emap : (X ⊙≃ Y) → (π'S n X ≃ᴳ π'S n Y)
  π'S-emap e = Trunc-group-emap (Ω^'S-group-structure-emap n e)

{- π_(n+1) of a space is π_n of its loop space -}
abstract
  πS-Ω-split-iso : ∀ {i} (n : ℕ) (X : Ptd i)
    → πS (S n) X ≃ᴳ πS n (⊙Ω X)
  πS-Ω-split-iso n X =
    group-hom
      (Trunc-fmap (Ω^-Ω-split (S n) X))
      (Trunc-elim
        (λ p → Trunc-elim
          (λ q → ap [_] (Ω^S-Ω-split-∙ n X p q)))) ,
    Trunc-isemap {n = 0} (Ω^-Ω-split-is-equiv (S n) X)

{- We can shift the truncation inside the loop in the definition of π -}
module _ {i} where

  private
    record Ω^STruncPreIso (n : ℕ) (m : ℕ₋₂) (k : ℕ₋₂) (X : Ptd i)
      : Type i where
      field
        F : ⊙Ω^ (S n) (⊙Trunc k X) ⊙→ ⊙Trunc m (⊙Ω^ (S n) X)
        pres-comp : ∀ (p q : Ω^ (S n) (⊙Trunc k X))
          → fst F (Ω^S-∙ n p q) == Trunc-fmap2 (Ω^S-∙ n) (fst F p) (fst F q)
        e : is-equiv (fst F)

    Ω^S-Trunc-preiso : (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
      → Ω^STruncPreIso n m (⟨ S n ⟩₋₂ +2+ m) X
    Ω^S-Trunc-preiso O m X =
      record { F = (–> (Trunc=-equiv [ pt X ] [ pt X ]) , idp);
               pres-comp = Trunc=-∙-comm;
               e = snd (Trunc=-equiv [ pt X ] [ pt X ]) }
    Ω^S-Trunc-preiso (S n) m X =
      let
        r : Ω^STruncPreIso n (S m) (⟨ S n ⟩₋₂ +2+ S m) X
        r = Ω^S-Trunc-preiso n (S m) X

        H = (–> (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]) , idp)
        G = ⊙Ω-fmap (Ω^STruncPreIso.F r)
      in
      transport (λ k → Ω^STruncPreIso (S n) m k X)
        (+2+-βr ⟨ S n ⟩₋₂ m)
        (record {
           F = H ⊙∘ G;
           pres-comp = λ p q →
             ap (fst H) (Ω^S-fmap-∙ 0 (Ω^STruncPreIso.F r) p q)
             ∙ (Trunc=-∙-comm (fst G p) (fst G q));
           e = snd (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]
                    ∘e Ω^-emap 1 (Ω^STruncPreIso.F r , Ω^STruncPreIso.e r))})

  Ω^S-group-Trunc-fuse-diag-iso : (n : ℕ) (X : Ptd i)
    → Ω^S-group n (⊙Trunc ⟨ S n ⟩ X) ≃ᴳ πS n X
  Ω^S-group-Trunc-fuse-diag-iso n X = group-hom (fst F) pres-comp , e
    where
    r = transport (λ k → Ω^STruncPreIso n 0 k X)
                  (+2+0 ⟨ S n ⟩₋₂) (Ω^S-Trunc-preiso n 0 X)
    open Ω^STruncPreIso r

{- favonia: the same lemma for the alternative homotopy groups is trivial. -}

  Ω^'S-group-Trunc-fuse-diag-iso : (n : ℕ) (X : Ptd i)
    → Ω^'S-group n (⊙Trunc ⟨ S n ⟩ X) ≃ᴳ π'S n X
  Ω^'S-group-Trunc-fuse-diag-iso O X =
    ≃-to-≃ᴳ (Trunc=-equiv [ pt X ] [ pt X ]) Trunc=-∙-comm
  Ω^'S-group-Trunc-fuse-diag-iso (S n) X =
        Ω^'S-group-Trunc-fuse-diag-iso n (⊙Ω X)
    ∘eᴳ Ω^'S-group-emap n {X = ⊙Ω (⊙Trunc ⟨ S (S n) ⟩ X)} (≃-to-⊙≃ (Trunc=-equiv [ pt X ] [ pt X ]) idp)

abstract
  πS-Trunc-fuse-≤-iso : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (⟨ S n ⟩ ≤T m) → πS n (⊙Trunc m X) ≃ᴳ πS n X
  πS-Trunc-fuse-≤-iso n m X Sn≤m =
    πS n (⊙Trunc m X)
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso n (⊙Trunc m X) ⁻¹ᴳ ⟩
    Ω^S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))
      ≃ᴳ⟨ Ω^S-group-emap n (≃-to-⊙≃ (Trunc-fuse-≤ (de⊙ X) Sn≤m) idp) ⟩
    Ω^S-group n (⊙Trunc ⟨ S n ⟩ X)
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso n X ⟩
    πS n X
      ≃ᴳ∎

  π'S-Trunc-fuse-≤-iso : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (⟨ S n ⟩ ≤T m) → π'S n (⊙Trunc m X) ≃ᴳ π'S n X
  π'S-Trunc-fuse-≤-iso n m X Sn≤m =
    π'S n (⊙Trunc m X)
      ≃ᴳ⟨ Ω^'S-group-Trunc-fuse-diag-iso n (⊙Trunc m X) ⁻¹ᴳ ⟩
    Ω^'S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))
      ≃ᴳ⟨ Ω^'S-group-emap n (≃-to-⊙≃ (Trunc-fuse-≤ (de⊙ X) Sn≤m) idp) ⟩
    Ω^'S-group n (⊙Trunc ⟨ S n ⟩ X)
      ≃ᴳ⟨ Ω^'S-group-Trunc-fuse-diag-iso n X ⟩
    π'S n X
      ≃ᴳ∎

  πS-Trunc-fuse->-iso : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → πS n (⊙Trunc m X) ≃ᴳ 0ᴳ
  πS-Trunc-fuse->-iso n m X m<n =
    πS n (⊙Trunc m X)
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso n (⊙Trunc m X) ⁻¹ᴳ ⟩
    Ω^S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))
      ≃ᴳ⟨ contr-iso-0ᴳ _ $ inhab-prop-is-contr
           (Group.ident (Ω^S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))))
           {{Ω^-level -1 (S n) _ $ Trunc-preserves-level ⟨ S n ⟩ $
             raise-level-≤T
               (transport (λ k → m ≤T k) (+2+-comm -1 ⟨ S n ⟩₋₂) (<T-to-≤T m<n))
               (Trunc-level {n = m})}} ⟩
    0ᴳ ≃ᴳ∎

  π'S-Trunc-fuse->-iso : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → π'S n (⊙Trunc m X) ≃ᴳ 0ᴳ
  π'S-Trunc-fuse->-iso n m X m<n =
    π'S n (⊙Trunc m X)
      ≃ᴳ⟨ Ω^'S-group-Trunc-fuse-diag-iso n (⊙Trunc m X) ⁻¹ᴳ ⟩
    Ω^'S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))
      ≃ᴳ⟨ contr-iso-0ᴳ _ $ inhab-prop-is-contr
           (Group.ident (Ω^'S-group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X))))
           {{Ω^'-is-prop (S n) _ $ Trunc-preserves-level ⟨ S n ⟩ $
             raise-level-≤T (<T-to-≤T m<n) (Trunc-level {n = m})}} ⟩
    0ᴳ ≃ᴳ∎

  -- XXX Naming conventions?
  πS->level-econv : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → {{_ : has-level m (de⊙ X)}}
    → πS n X ≃ᴳ 0ᴳ
  πS->level-econv n m X lt =
    πS n X
      ≃ᴳ⟨ πS-emap n (⊙unTrunc-equiv X ⊙⁻¹) ⟩
    πS n (⊙Trunc m X)
      ≃ᴳ⟨ πS-Trunc-fuse->-iso n m X lt ⟩
    0ᴳ
      ≃ᴳ∎

  π'S->level-econv : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → {{_ : has-level m (de⊙ X)}}
    → π'S n X ≃ᴳ 0ᴳ
  π'S->level-econv n m X lt =
    π'S n X
      ≃ᴳ⟨ π'S-emap n (⊙unTrunc-equiv X ⊙⁻¹) ⟩
    π'S n (⊙Trunc m X)
      ≃ᴳ⟨ π'S-Trunc-fuse->-iso n m X lt ⟩
    0ᴳ
      ≃ᴳ∎

{- πₙ(X × Y) == πₙ(X) × πₙ(Y) -}
module _ {i j} (n : ℕ) (X : Ptd i) (Y : Ptd  j) where

  πS-× : πS n (X ⊙× Y) ≃ᴳ πS n X ×ᴳ πS n Y
  πS-× = Trunc-group-× _ _ ∘eᴳ Trunc-group-emap (Ω^S-group-structure-× n X Y)

  π'S-× : π'S n (X ⊙× Y) ≃ᴳ π'S n X ×ᴳ π'S n Y
  π'S-× = Trunc-group-× _ _ ∘eᴳ Trunc-group-emap (Ω^'S-group-structure-× n X Y)
