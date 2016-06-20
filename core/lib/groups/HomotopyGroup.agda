{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Empty
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.types.Pointed
open import lib.types.Group
open import lib.types.LoopSpace
open import lib.groups.TruncationGroup
open import lib.groups.GroupProduct
open import lib.groups.Homomorphisms
open import lib.groups.Unit

module lib.groups.HomotopyGroup where

{- Higher homotopy groups -}
module _ {i} where

  πS : (n : ℕ) (X : Ptd i) → Group i
  πS n X = Trunc-Group (Ω^S-group-structure n X)

  fundamental-group : (X : Ptd i) → Group i
  fundamental-group X = πS 0 X

{- π_(n+1) of a space is π_n of its loop space -}
abstract
  πS-inner-iso : ∀ {i} (n : ℕ) (X : Ptd i)
    → πS (S n) X == πS n (⊙Ω X)
  πS-inner-iso n X = group-ua
    (record {
       f = Trunc-fmap (Ω^-inner-out (S n) X);
       pres-comp =
         Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
           (λ p → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
              (λ q → ap [_] (Ω^S-inner-out-conc^S n X p q)))} ,
     is-equiv-Trunc 0 (Ω^-inner-out (S n) X) (Ω^-inner-is-equiv (S n) X))

{- We can shift the truncation inside the loop in the definition of π -}
module _ {i} where

  private
    record Ω^STs-PreIso (m : ℕ₋₂) (n : ℕ) (k : ℕ₋₂) (X : Ptd i)
      : Type i where
      field
        F : fst (⊙Ω^ (S n) (⊙Trunc k X) ⊙→ ⊙Trunc m (⊙Ω^ (S n) X))
        pres-comp : ∀ (p q : Ω^ (S n) (⊙Trunc k X))
          → fst F (conc^S n p q) == Trunc-fmap2 (conc^S n) (fst F p) (fst F q)
        e : is-equiv (fst F)

    Ω^S-Trunc-shift-preiso : (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
      → Ω^STs-PreIso m n (⟨ S n ⟩₋₂ +2+ m) X
    Ω^S-Trunc-shift-preiso O m X =
      record { F = (–> (Trunc=-equiv [ snd X ] [ snd X ]) , idp);
               pres-comp = Trunc=-∙-comm;
               e = snd (Trunc=-equiv [ snd X ] [ snd X ]) }
    Ω^S-Trunc-shift-preiso (S n) m X =
      let
        r : Ω^STs-PreIso (S m) n (⟨ S n ⟩₋₂ +2+ S m) X
        r = Ω^S-Trunc-shift-preiso n (S m) X

        H = (–> (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]) , idp)
        G = ap^ 1 (Ω^STs-PreIso.F r)
      in
      transport (λ k → Ω^STs-PreIso m (S n) k X)
        (+2+-βr ⟨ S n ⟩₋₂ m)
        (record {
           F = H ⊙∘ G;
           pres-comp = λ p q →
             ap (fst H) (ap^S-conc^S 0 (Ω^STs-PreIso.F r) p q)
             ∙ (Trunc=-∙-comm (fst G p) (fst G q));
           e = snd (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]
                    ∘e equiv-ap^ 1 (Ω^STs-PreIso.F r) (Ω^STs-PreIso.e r))})

  πS-Trunc-shift-iso : (n : ℕ) (X : Ptd i)
    → Ω^S-Group n (⊙Trunc ⟨ S n ⟩ X) Trunc-level == πS n X
  πS-Trunc-shift-iso n X = group-ua (group-hom (fst F) pres-comp , e)
    where
    n-eq : ∀ (n : ℕ) → ⟨ n ⟩₋₂ +2+ 0 == ⟨ n ⟩
    n-eq O = idp
    n-eq (S n) = ap S (n-eq n)

    r = transport (λ k → Ω^STs-PreIso 0 n k X)
                  (n-eq (S n)) (Ω^S-Trunc-shift-preiso n 0 X)
    open Ω^STs-PreIso r

abstract
  πS-below-trunc : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (⟨ S n ⟩ ≤T m) → πS n (⊙Trunc m X) == πS n X
  πS-below-trunc n m X lte =
    πS n (⊙Trunc m X)
      =⟨ ! (πS-Trunc-shift-iso n (⊙Trunc m X)) ⟩
    Ω^S-Group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X)) Trunc-level
      =⟨ lemma ⟩
    Ω^S-Group n (⊙Trunc ⟨ S n ⟩ X) Trunc-level
      =⟨ πS-Trunc-shift-iso n X ⟩
    πS n X ∎
    where
    lemma : Ω^S-Group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X)) Trunc-level
         ==  Ω^S-Group n (⊙Trunc ⟨ S n ⟩ X) Trunc-level
    lemma = ap (uncurry $ Ω^S-Group n) $
      pair=
        (⊙ua (⊙≃-in (fuse-Trunc (fst X) ⟨ S n ⟩ m) idp) ∙
         ap (λ k → ⊙Trunc k X) (minT-out-l lte))
        (prop-has-all-paths-↓ has-level-is-prop)

  πS-above-trunc : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → πS n (⊙Trunc m X) == 0ᴳ
  πS-above-trunc n m X lt =
    πS n (⊙Trunc m X)
      =⟨ ! (πS-Trunc-shift-iso n (⊙Trunc m X)) ⟩
    Ω^S-Group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X)) Trunc-level
      =⟨ contr-is-0ᴳ _ $ inhab-prop-is-contr
           (Group.ident (Ω^S-Group n (⊙Trunc ⟨ S n ⟩ (⊙Trunc m X)) Trunc-level))
           (Ω^-level-in -1 (S n) _ $ Trunc-preserves-level ⟨ S n ⟩ $
             raise-level-≤T
               (transport (λ k → m ≤T k) (+2+-comm -1 ⟨ S n ⟩₋₂) (<T-to-≤T lt))
               (Trunc-level {n = m})) ⟩
    0ᴳ ∎

  πS-above-level : ∀ {i} (n : ℕ) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ S n ⟩) → has-level m (fst X)
    → πS n X == 0ᴳ
  πS-above-level n m X lt pX =
    ap (πS n) (! (⊙ua (⊙≃-in (unTrunc-equiv _ pX) idp)))
    ∙ πS-above-trunc n m X lt

{- πₙ(X × Y) == πₙ(X) × πₙ(Y) -}
module _ {i j} (n : ℕ) (X : Ptd i) (Y : Ptd  j) where

  πS-× : πS n (X ⊙× Y) == πS n X ×ᴳ πS n Y
  πS-× =
    group-ua (Trunc-Group-iso f pres-comp (is-eq f g f-g g-f))
    ∙ Trunc-Group-× _ _
    where
    f : Ω^ (S n) (X ⊙× Y) → Ω^ (S n) X × Ω^ (S n) Y
    f r = (fst (ap^ (S n) ⊙fst) r , fst (ap^ (S n) ⊙snd) r)

    g : Ω^ (S n) X × Ω^ (S n) Y → Ω^ (S n) (X ⊙× Y)
    g = fst (ap2^ (S n) (⊙idf _))

    f-g : (s : Ω^ (S n) X × Ω^ (S n) Y) → f (g s) == s
    f-g (p , q) = pair×=
      (app= (ap fst (ap^-ap2^ (S n) ⊙fst (⊙idf _) ∙ ap2^-fst (S n))) (p , q))
      (app= (ap fst (ap^-ap2^ (S n) ⊙snd (⊙idf _) ∙ ap2^-snd (S n))) (p , q))

    g-f : (r : Ω^ (S n) (X ⊙× Y)) → g (f r) == r
    g-f = app= $ ap fst $
      ap (λ h → h ⊙∘ ⊙diag) (ap2^-ap^ (S n) (⊙idf _) ⊙fst ⊙snd)
      ∙ ap2^-diag (S n) (⊙idf _ ⊙∘ pair⊙→ ⊙fst ⊙snd)
      ∙ ap^-idf (S n)

    pres-comp : (p q : Ω^ (S n) (X ⊙× Y))
      → f (conc^S n p q) == (conc^S n (fst (f p)) (fst (f q)) ,
                             conc^S n (snd (f p)) (snd (f q)))
    pres-comp p q = pair×= (ap^S-conc^S n ⊙fst p q) (ap^S-conc^S n ⊙snd p q)
