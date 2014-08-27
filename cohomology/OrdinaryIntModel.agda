{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.WithCoefficients
open import cohomology.Exactness
open import cohomology.Choice
open import cohomology.OrdinaryTheory

module cohomology.OrdinaryIntModel
  {i} (G : Group i) (G-abelian : is-abelian G) where

import cohomology.OrdinaryNatModel G G-abelian as ℕM

C : (n : ℤ) (X : Ptd i) → Group i
C O X = ℕM.C O X
C (pos m) X = ℕM.C (S m) X
C (neg _) X = 0G

C-abelian : (n : ℤ) (X : Ptd i) → is-abelian (C n X)
C-abelian O X = ℕM.C-abelian O X
C-abelian (pos m) X = ℕM.C-abelian (S m) X
C-abelian (neg _) X = λ _ _ → idp

CF-hom : (n : ℤ) {X Y : Ptd i} → fst (X ∙→ Y) → GroupHom (C n Y) (C n X)
CF-hom O F = ℕM.CF-hom O F
CF-hom (pos m) F = ℕM.CF-hom (S m) F
CF-hom (neg m) _ = cst-hom

CF-ident : (n : ℤ) {X : Ptd i} → CF-hom n (ptd-idf X) == idhom (C n X)
CF-ident O {X} = ℕM.CF-ident O {X}
CF-ident (pos m) {X} = ℕM.CF-ident (S m) {X}
CF-ident (neg m) = idp

CF-comp : (n : ℤ) {X Y Z : Ptd i} (G : fst (Y ∙→ Z)) (F : fst (X ∙→ Y))
  → CF-hom n (G ∘ptd F) == CF-hom n F ∘hom CF-hom n G
CF-comp O G F = ℕM.CF-comp O G F
CF-comp (pos m) G F = ℕM.CF-comp (S m) G F
CF-comp (neg m) G F = idp

C-Susp : (n : ℤ) (X : Ptd i) → C (succ n) (Ptd-Susp X) == C n X
C-Susp O X = ℕM.C-SuspS O X
C-Susp (pos m) X = ℕM.C-SuspS (S m) X
C-Susp (neg O) X = ℕM.C-SuspO X
C-Susp (neg (S m)) X = idp

C-exact : (n : ℤ) {X Y : Ptd i} (f : fst (X ∙→ Y))
  → is-exact (GroupHom.ptd-f (CF-hom n (ptd-cfcod f)))
             (GroupHom.ptd-f (CF-hom n f))
C-exact O f = ℕM.C-exact O f
C-exact (pos m) f = ℕM.C-exact (S m) f
C-exact (neg m) f =
  record {itok = λ _ _ → idp; ktoi = λ _ _ → [ _ , idp ]}

C-additive : (n : ℤ) {A : Type i} (X : A → Ptd i)
  (ac : (W : A → Type i) → (∀ a → has-level (ℤ-to-ℕ₋₂ n) (W a))
                         → has-choice ⟨0⟩ A W)
  → C n (Ptd-BigWedge X) == ΠG A (C n ∘ X)
C-additive O X ac = ℕM.C-additive O X ac
C-additive (pos m) X ac = ℕM.C-additive (S m) X ac
C-additive (neg m) {A = A} X ac =
  ! (contr-iso-LiftUnit (ΠG A (λ _ → 0G))
      (Π-level (λ _ → Lift-level {j = i} Unit-is-contr)))

C-dimension : (n : ℤ) → n ≠ O → C n (Ptd-Sphere 0) == 0G
C-dimension O neq = ⊥-rec (neq idp)
C-dimension (pos m) neq = ℕM.C-dimension-S m
C-dimension (neg m) neq = idp

C-Cohomology : OrdinaryTheory i
C-Cohomology = record {
  C = C;
  CF-hom = CF-hom;
  CF-ident = CF-ident;
  CF-comp = CF-comp;
  C-abelian = C-abelian;
  C-Susp = C-Susp;
  C-exact = C-exact;
  C-additive = C-additive;
  C-dimension = C-dimension}
