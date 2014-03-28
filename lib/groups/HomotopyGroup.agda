{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Empty
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.Pointed
open import lib.types.Group
open import lib.types.LoopSpace

open import lib.groups.TruncationGroup

module lib.groups.HomotopyGroup where

{- Higher homotopy groups -}
module _ {i} where

  π-concrete : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) → Group i
  π-concrete n X = Trunc-Group (Ω^-group-structure n X)

  {- Since the definition of π-concrete is so complicated, using it 
   - can be very slow, so we use an abstracted version and convert
   - between the two when we need to expand π -}
  abstract
    π : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) → Group i
    π = π-concrete

    π-fold : π-concrete == π
    π-fold = idp

    π-unfold : π == π-concrete
    π-unfold = idp

  fundamental-group : (X : Ptd i) → Group i
  fundamental-group X = π 1 ⦃ ℕ-S≠O#instance ⦄ X

  {- Favonia: Sorry about this dirty workaround.
   - I should have updated covering spaces accordingly instead. -}
  concrete-fundamental-group : (X : Ptd i) → Group i
  concrete-fundamental-group X = π-concrete 1 ⦃ ℕ-S≠O#instance ⦄ X

{- π_(n+1) of a space is π_n of its loop space -}
abstract
  π-inner-iso : ∀ {i} (n : ℕ) ⦃ pn : n ≠ 0 ⦄ ⦃ psn : S n ≠ 0 ⦄ (X : Ptd i)
    → π (S n) ⦃ psn ⦄ X == π n ⦃ pn ⦄ (Ptd-Ω X)
  π-inner-iso O ⦃ pn ⦄ ⦃ psn ⦄ X = ⊥-rec (pn idp)
  π-inner-iso (S n') ⦃ pn' ⦄ ⦃ pn ⦄ X = 
    transport (λ pi → pi (S n) ⦃ pn ⦄ X == pi n ⦃ pn' ⦄ (Ptd-Ω X)) π-fold $ 
      group-iso
        (record { 
          f = Trunc-fmap (Ω^-inner-out n X);
          pres-ident = ap [_] (snd (Ptd-Ω^-inner-out n X));
          pres-comp = 
            Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
              (λ p → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
                 (λ q → ap [_] (Ω^-inner-out-conc^ n ⦃ pn' ⦄ X p q)))})
        (is-equiv-Trunc ⟨0⟩ (Ω^-inner-out n X) (Ω^-inner-is-equiv n X))
    where
    n : ℕ
    n = S n'

{- We can shift the truncation inside the loop in the definition of π -}
module _ {i} where

  private
    record Ω^Ts-PreIso (m : ℕ₋₂) (n : ℕ) (k : ℕ₋₂) ⦃ _ : n ≠ O ⦄ (X : Ptd i) 
      : Type i where
      field
        F : fst (Ptd-Ω^ n (Ptd-Trunc k X) ∙→ Ptd-Trunc m (Ptd-Ω^ n X))
        pres-comp : ∀ (p q : Ω^ n (Ptd-Trunc k X)) 
          → fst F (conc^ n p q) == Trunc-fmap2 (conc^ n) (fst F p) (fst F q)
        e : is-equiv (fst F)

    Ω^-Trunc-shift-preiso : (n : ℕ) (m : ℕ₋₂) ⦃ _ : n ≠ O ⦄ (X : Ptd i) 
      → Ω^Ts-PreIso m n ((n -2) +2+ m) X
    Ω^-Trunc-shift-preiso O m ⦃ posi ⦄ X = ⊥-rec (posi idp)
    Ω^-Trunc-shift-preiso (S O) m X = 
      record { F = (–> (Trunc=-equiv [ snd X ] [ snd X ]) , idp); 
               pres-comp = Trunc=-∙-comm; 
               e = snd (Trunc=-equiv [ snd X ] [ snd X ]) }
    Ω^-Trunc-shift-preiso (S (S n)) m X = 
      let
        r : Ω^Ts-PreIso (S m) (S n) ((S n -2) +2+ S m) X
        r = Ω^-Trunc-shift-preiso (S n) (S m) X

        H = (–> (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]) , idp)
        G = ap^ 1 (Ω^Ts-PreIso.F r)
      in
      transport (λ k → Ω^Ts-PreIso m (S (S n)) k X) (+2+-βr (S n -2) m) $
        record { 
          F = H ∘ptd G;
          pres-comp = λ p q → 
            ap (fst H) (ap^-conc^ 1 (Ω^Ts-PreIso.F r) p q) 
            ∙ (Trunc=-∙-comm (fst G p) (fst G q)); 
          e = snd (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ] 
                   ∘e equiv-ap^ 1 (Ω^Ts-PreIso.F r) (Ω^Ts-PreIso.e r)) }

  π-Trunc-shift-iso : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) 
    → Ω^-Group n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level == π n X 
  π-Trunc-shift-iso n X = transport 
    (λ pi → Ω^-Group n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level == pi n X) 
    π-fold 
    (group-iso (group-hom (fst F) (snd F) pres-comp) e)
    where 
    n-eq : ∀ (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
    n-eq O = idp
    n-eq (S n) = ap S (n-eq n)

    r = transport (λ k → Ω^Ts-PreIso ⟨0⟩ n k X) 
                  (n-eq n) (Ω^-Trunc-shift-preiso n ⟨0⟩ X)
    open Ω^Ts-PreIso r

abstract
  π-Trunc-≤T-iso : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (m : ℕ₋₂) (X : Ptd i)
    → (⟨ n ⟩ ≤T m) → π n (Ptd-Trunc m X) == π n X
  π-Trunc-≤T-iso n m X lte = 
    π n (Ptd-Trunc m X) 
      =⟨ ! (π-Trunc-shift-iso n (Ptd-Trunc m X)) ⟩
    Ω^-Group n (Ptd-Trunc ⟨ n ⟩ (Ptd-Trunc m X)) Trunc-level
      =⟨ lemma ⟩
    Ω^-Group n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level
      =⟨ π-Trunc-shift-iso n X ⟩
    π n X ∎
    where
    lemma : Ω^-Group n (Ptd-Trunc ⟨ n ⟩ (Ptd-Trunc m X)) Trunc-level
         ==  Ω^-Group n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level
    lemma = ap (uncurry $ Ω^-Group n) $
      pair= 
        (ptd-ua (fuse-Trunc (fst X) ⟨ n ⟩ m) idp ∙ 
         ap (λ k → Ptd-Trunc k X) (minT-out-l lte)) 
        (prop-has-all-paths-↓ has-level-is-prop)
