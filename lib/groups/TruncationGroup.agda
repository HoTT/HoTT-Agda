{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.GroupProduct
open import lib.groups.Homomorphisms

module lib.groups.TruncationGroup where

module _ {i} {El : Type i} (GS : GroupStructure El) where

  Trunc-group-struct : GroupStructure (Trunc ⟨0⟩ El)
  Trunc-group-struct = record {
    ident = [ ident GS ];
    inv = Trunc-fmap (inv GS);
    comp = Trunc-fmap2 (comp GS);
    unitl =
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ unitl GS);
    unitr =
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ unitr GS);
    assoc = Trunc-elim
      (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)))
      (λ a → Trunc-elim
        (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
        (λ b → Trunc-elim
           (λ _ → =-preserves-level _ Trunc-level)
           (λ c → ap [_] (assoc GS a b c))));
    invl =
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ invl GS);
    invr =
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ invr GS) }
    where open GroupStructure

  Trunc-Group : Group i
  Trunc-Group = record {
    El = Trunc ⟨0⟩ El;
    El-level = Trunc-level;
    group-struct = Trunc-group-struct }

Trunc-Group-× : ∀ {i j} {A : Type i} {B : Type j}
  (GS : GroupStructure A) (HS : GroupStructure B)
  → Trunc-Group (×-group-struct GS HS)
    == Trunc-Group GS ×G Trunc-Group HS
Trunc-Group-× GS HS = group-iso
  (record {
    f = Trunc-rec (×-level Trunc-level Trunc-level)
          (λ {(a , b) → ([ a ] , [ b ])});
    pres-comp =
      Trunc-elim
        (λ _ → (Π-level (λ _ → =-preserves-level _
                                 (×-level Trunc-level Trunc-level))))
        (λ a → Trunc-elim
          (λ _ → =-preserves-level _ (×-level Trunc-level Trunc-level))
          (λ b → idp))})
  (is-eq _
    (uncurry (Trunc-rec (→-level Trunc-level)
               (λ a → Trunc-rec Trunc-level (λ b → [ a , b ]))))
    (uncurry (Trunc-elim
               (λ _ → Π-level (λ _ → =-preserves-level _
                                       (×-level Trunc-level Trunc-level)))
               (λ a → Trunc-elim
                        (λ _ → =-preserves-level _
                                 (×-level Trunc-level Trunc-level))
                        (λ b → idp))))
    (Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (λ _ → idp)))

Trunc-Group-iso : ∀ {i} {A B : Type i}
  {GS : GroupStructure A} {HS : GroupStructure B} (f : A → B)
  → ((a₁ a₂ : A) → f (GroupStructure.comp GS a₁ a₂)
                   == GroupStructure.comp HS (f a₁) (f a₂))
  → is-equiv f → Trunc-Group GS == Trunc-Group HS
Trunc-Group-iso f pres-comp ie = group-iso
  (record {
    f = Trunc-fmap f;
    pres-comp =
      Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
        (λ a₁ → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
          (λ a₂ → ap [_] (pres-comp a₁ a₂)))})
  (is-eq _ (Trunc-fmap (is-equiv.g ie))
    (Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
      (λ b → ap [_] (is-equiv.f-g ie b)))
    (Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
      (λ a → ap [_] (is-equiv.g-f ie a))))
