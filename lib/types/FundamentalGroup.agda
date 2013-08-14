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

module lib.types.FundamentalGroup where

{- Fundamental group -}
module _ {i} where

  π : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) → Group (Trunc ⟨0⟩ (Ω^ n X))
  π n X = record {
    El-level = Trunc-level;
    ident = ident; inv = inv; comp = comp;
    unitl = unitl; unitr = unitr; assoc = assoc;
    invr = invr; invl = invl }
    where
    ident : Trunc ⟨0⟩ (Ω^ n X)
    ident = [ idp^ n ]

    inv : Trunc ⟨0⟩ (Ω^ n X) → Trunc ⟨0⟩ (Ω^ n X)
    inv = Trunc-fmap (!^ n)

    comp : Trunc ⟨0⟩ (Ω^ n X) → Trunc ⟨0⟩ (Ω^ n X) → Trunc ⟨0⟩ (Ω^ n X)
    comp = Trunc-fmap2 (conc^ n)

    abstract
      unitl : ∀ a → comp ident a == a
      unitl = Trunc-elim
        (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ conc^-unit-l n)

      unitr : ∀ a → comp a ident == a
      unitr = Trunc-elim 
        (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ conc^-unit-r n)

      assoc : ∀ a b c → comp (comp a b) c == comp a (comp b c)
      assoc = Trunc-elim 
        (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)))
        (λ a → Trunc-elim
          (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
          (λ b → Trunc-elim 
             (λ _ → =-preserves-level _ Trunc-level) 
             (λ c → ap [_] (conc^-assoc n a b c))))

      invr : ∀ a → (comp a (inv a)) == ident
      invr = Trunc-elim
        (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ !^-inv-r n)

      invl : ∀ a → (comp (inv a) a) == ident
      invl = Trunc-elim
        (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ !^-inv-l n)

  πΣ : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) → Σ (Type i) Group
  πΣ n X = (Trunc ⟨0⟩ (Ω^ n X) , π n X)

{- π_(n+1) of a space is π_n of its loop space -}
abstract
  π-inner-iso : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i)
    → πΣ (S n) X == πΣ n (Ptd-Ω X)
  π-inner-iso O ⦃ posi ⦄ X = ⊥-rec (posi idp)
  π-inner-iso (S n') ⦃ posi ⦄ X = group-iso 
    (record { 
       f = Trunc-fmap (Ω^-inner-out n X);
       pres-ident = ap [_] (snd (Ptd-Ω^-inner-out n X));
       pres-comp = 
         Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
           (λ p → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
              (λ q → ap [_] (Ω^-inner-out-conc^ n ⦃ posi ⦄ X p q)))})
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
    → Ω^-groupΣ n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level == πΣ n X 
  π-Trunc-shift-iso n X = group-iso 
    (record {f = fst F; pres-ident = snd F; pres-comp = pres-comp })
    e
    where 
    n-eq : ∀ (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
    n-eq O = idp
    n-eq (S n) = ap S (n-eq n)

    r = transport (λ k → Ω^Ts-PreIso ⟨0⟩ n k X) 
                  (n-eq n) (Ω^-Trunc-shift-preiso n ⟨0⟩ X)
    open Ω^Ts-PreIso r

π-Trunc-≤T-iso : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (m : ℕ₋₂) (X : Ptd i)
  → (⟨ n ⟩ ≤T m) → πΣ n (Ptd-Trunc m X) == πΣ n X
π-Trunc-≤T-iso n m X lte = 
  πΣ n (Ptd-Trunc m X) 
    =⟨ ! (π-Trunc-shift-iso n (Ptd-Trunc m X)) ⟩
  Ω^-groupΣ n (Ptd-Trunc ⟨ n ⟩ (Ptd-Trunc m X)) Trunc-level
    =⟨ lemma ⟩
  Ω^-groupΣ n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level
    =⟨ π-Trunc-shift-iso n X ⟩
  πΣ n X ∎
  where
  lemma : Ω^-groupΣ n (Ptd-Trunc ⟨ n ⟩ (Ptd-Trunc m X)) Trunc-level
       ==  Ω^-groupΣ n (Ptd-Trunc ⟨ n ⟩ X) Trunc-level
  lemma = ap (uncurry $ Ω^-groupΣ n) $
    pair= 
      (ptd-ua (fuse-Trunc (fst X) ⟨ n ⟩ m) idp ∙ 
       ap (λ k → Ptd-Trunc k X) (minT-out-l lte)) 
      (prop-has-all-paths-↓ has-level-is-prop)
