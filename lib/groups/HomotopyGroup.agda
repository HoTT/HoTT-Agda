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

  π : (n : ℕ) (t : n ≠ O) (X : Ptd i) → Group i
  π n t X = Trunc-Group (Ω^-group-structure n t X)

  fundamental-group : (X : Ptd i) → Group i
  fundamental-group X = π 1 (ℕ-S≠O _) X

{- π_(n+1) of a space is π_n of its loop space -}
abstract
  π-inner-iso : ∀ {i} (n : ℕ) (tn : n ≠ 0) (tsn : S n ≠ 0) (X : Ptd i)
    → π (S n) tsn X == π n tn (⊙Ω X)
  π-inner-iso O tn tsn X = ⊥-rec (tn idp)
  π-inner-iso (S n') tn' tn X =
    group-iso
      (record {
        f = Trunc-fmap (Ω^-inner-out n X);
        pres-comp =
          Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
            (λ p → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
               (λ q → ap [_] (Ω^-inner-out-conc^ n tn' X p q)))})
      (is-equiv-Trunc ⟨0⟩ (Ω^-inner-out n X) (Ω^-inner-is-equiv n X))
    where
    n : ℕ
    n = S n'

{- We can shift the truncation inside the loop in the definition of π -}
module _ {i} where

  private
    record Ω^Ts-PreIso (m : ℕ₋₂) (n : ℕ) (k : ℕ₋₂) (t : n ≠ O) (X : Ptd i)
      : Type i where
      field
        F : fst (⊙Ω^ n (⊙Trunc k X) ⊙→ ⊙Trunc m (⊙Ω^ n X))
        pres-comp : ∀ (p q : Ω^ n (⊙Trunc k X))
          → fst F (conc^ n t p q) == Trunc-fmap2 (conc^ n t) (fst F p) (fst F q)
        e : is-equiv (fst F)

    Ω^-Trunc-shift-preiso : (n : ℕ) (m : ℕ₋₂) (t : n ≠ O) (X : Ptd i)
      → Ω^Ts-PreIso m n ((n -2) +2+ m) t X
    Ω^-Trunc-shift-preiso O m t X = ⊥-rec (t idp)
    Ω^-Trunc-shift-preiso (S O) m _ X =
      record { F = (–> (Trunc=-equiv [ snd X ] [ snd X ]) , idp);
               pres-comp = Trunc=-∙-comm;
               e = snd (Trunc=-equiv [ snd X ] [ snd X ]) }
    Ω^-Trunc-shift-preiso (S (S n)) m t X =
      let
        r : Ω^Ts-PreIso (S m) (S n) ((S n -2) +2+ S m) (ℕ-S≠O _) X
        r = Ω^-Trunc-shift-preiso (S n) (S m) (ℕ-S≠O _) X

        H = (–> (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]) , idp)
        G = ap^ 1 (Ω^Ts-PreIso.F r)
      in
      transport (λ k → Ω^Ts-PreIso m (S (S n)) k t X)
        (+2+-βr (S n -2) m)
        (record {
           F = H ⊙∘ G;
           pres-comp = λ p q →
             ap (fst H) (ap^-conc^ 1 (ℕ-S≠O _) (Ω^Ts-PreIso.F r) p q)
             ∙ (Trunc=-∙-comm (fst G p) (fst G q));
           e = snd (Trunc=-equiv [ idp^ (S n) ] [ idp^ (S n) ]
                    ∘e equiv-ap^ 1 (Ω^Ts-PreIso.F r) (Ω^Ts-PreIso.e r))})

  π-Trunc-shift-iso : (n : ℕ) (t : n ≠ O) (X : Ptd i)
    → Ω^-Group n t (⊙Trunc ⟨ n ⟩ X) Trunc-level == π n t X
  π-Trunc-shift-iso n t X = group-iso (group-hom (fst F) pres-comp) e
    where
    n-eq : ∀ (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
    n-eq O = idp
    n-eq (S n) = ap S (n-eq n)

    r = transport (λ k → Ω^Ts-PreIso ⟨0⟩ n k t X)
                  (n-eq n) (Ω^-Trunc-shift-preiso n ⟨0⟩ t X)
    open Ω^Ts-PreIso r

abstract
  π-below-trunc : ∀ {i} (n : ℕ) (t : n ≠ O) (m : ℕ₋₂) (X : Ptd i)
    → (⟨ n ⟩ ≤T m) → π n t (⊙Trunc m X) == π n t X
  π-below-trunc n t m X lte =
    π n t (⊙Trunc m X)
      =⟨ ! (π-Trunc-shift-iso n t (⊙Trunc m X)) ⟩
    Ω^-Group n t (⊙Trunc ⟨ n ⟩ (⊙Trunc m X)) Trunc-level
      =⟨ lemma ⟩
    Ω^-Group n t (⊙Trunc ⟨ n ⟩ X) Trunc-level
      =⟨ π-Trunc-shift-iso n t X ⟩
    π n t X ∎
    where
    lemma : Ω^-Group n t (⊙Trunc ⟨ n ⟩ (⊙Trunc m X)) Trunc-level
         ==  Ω^-Group n t (⊙Trunc ⟨ n ⟩ X) Trunc-level
    lemma = ap (uncurry $ Ω^-Group n t) $
      pair=
        (⊙ua (fuse-Trunc (fst X) ⟨ n ⟩ m) idp ∙
         ap (λ k → ⊙Trunc k X) (minT-out-l lte))
        (prop-has-all-paths-↓ has-level-is-prop)

  π-above-trunc : ∀ {i} (n : ℕ) (t : n ≠ O) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ n ⟩) → π n t (⊙Trunc m X) == 0G
  π-above-trunc n t m X lt =
    π n t (⊙Trunc m X)
      =⟨ ! (π-Trunc-shift-iso n t (⊙Trunc m X)) ⟩
    Ω^-Group n t (⊙Trunc ⟨ n ⟩ (⊙Trunc m X)) Trunc-level
      =⟨ contr-iso-LiftUnit _ $ inhab-prop-is-contr
           (Group.ident (Ω^-Group n t (⊙Trunc ⟨ n ⟩ (⊙Trunc m X)) Trunc-level))
           (Ω^-level-in ⟨-1⟩ n _ $ Trunc-preserves-level ⟨ n ⟩ $
             raise-level-≤T
               (transport (λ k → m ≤T k) (+2+-comm ⟨-1⟩ (n -2)) (<T-to-≤T lt))
               (Trunc-level {n = m})) ⟩
    0G ∎

  π-above-level : ∀ {i} (n : ℕ) (t : n ≠ O) (m : ℕ₋₂) (X : Ptd i)
    → (m <T ⟨ n ⟩) → has-level m (fst X)
    → π n t X == 0G
  π-above-level n t m X lt pX =
    ap (π n t) (! (⊙ua (unTrunc-equiv _ pX) idp))
    ∙ π-above-trunc n t m X lt

{- πₙ(X × Y) == πₙ(X) × πₙ(Y) -}
module _ {i j} (n : ℕ) (t : n ≠ O) (X : Ptd i) (Y : Ptd  j) where

  π-× : π n t (X ⊙× Y) == π n t X ×G π n t Y
  π-× =
    Trunc-Group-iso f pres-comp (is-eq f g f-g g-f)
    ∙ Trunc-Group-× _ _
    where
    f : Ω^ n (X ⊙× Y) → Ω^ n X × Ω^ n Y
    f r = (fst (ap^ n ⊙fst) r , fst (ap^ n ⊙snd) r)

    g : Ω^ n X × Ω^ n Y → Ω^ n (X ⊙× Y)
    g = fst (ap2^ n (⊙idf _))

    f-g : (s : Ω^ n X × Ω^ n Y) → f (g s) == s
    f-g (p , q) = pair×=
      (app= (ap fst (ap^-ap2^ n ⊙fst (⊙idf _) ∙ ap2^-fst n)) (p , q))
      (app= (ap fst (ap^-ap2^ n ⊙snd (⊙idf _) ∙ ap2^-snd n)) (p , q))

    g-f : (r : Ω^ n (X ⊙× Y)) → g (f r) == r
    g-f = app= $ ap fst $
      ap (λ h → h ⊙∘ ⊙diag) (ap2^-ap^ n (⊙idf _) ⊙fst ⊙snd)
      ∙ ap2^-diag n (⊙idf _ ⊙∘ pair⊙→ ⊙fst ⊙snd)
      ∙ ap^-idf n

    pres-comp : (p q : Ω^ n (X ⊙× Y))
      → f (conc^ n t p q) == (conc^ n t (fst (f p)) (fst (f q)) ,
                              conc^ n t (snd (f p)) (snd (f q)))
    pres-comp p q = pair×= (ap^-conc^ n t ⊙fst p q) (ap^-conc^ n t ⊙snd p q)
