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
    comp = _⊗_;
    unitl = t-unitl;
    unitr = t-unitr;
    assoc = t-assoc;
    invl = t-invl;
    invr = t-invr}
    where
    open GroupStructure
    infix 80 _⊗_
    _⊗_ = Trunc-fmap2 (comp GS)

    abstract
      t-unitl : (t : Trunc ⟨0⟩ El) → [ ident GS ] ⊗ t == t
      t-unitl = Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ unitl GS)

      t-unitr : (t : Trunc ⟨0⟩ El) → t ⊗ [ ident GS ] == t
      t-unitr = Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ unitr GS)

      t-assoc : (t₁ t₂ t₃ : Trunc ⟨0⟩ El) → (t₁ ⊗ t₂) ⊗ t₃ == t₁ ⊗ (t₂ ⊗ t₃)
      t-assoc = Trunc-elim
        (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)))
        (λ a → Trunc-elim
          (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
          (λ b → Trunc-elim
             (λ _ → =-preserves-level _ Trunc-level)
             (λ c → ap [_] (assoc GS a b c))))

      t-invl : (t : Trunc ⟨0⟩ El) → Trunc-fmap (inv GS) t ⊗ t == [ ident GS ]
      t-invl = Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ invl GS)

      t-invr : (t : Trunc ⟨0⟩ El) → t ⊗ Trunc-fmap (inv GS) t == [ ident GS ]
      t-invr = Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
        (ap [_] ∘ invr GS)


  Trunc-Group : Group i
  Trunc-Group = record {
    El = Trunc ⟨0⟩ El;
    El-level = Trunc-level;
    group-struct = Trunc-group-struct }

Trunc-Group-× : ∀ {i j} {A : Type i} {B : Type j}
  (GS : GroupStructure A) (HS : GroupStructure B)
  → Trunc-Group (×-group-struct GS HS) == Trunc-Group GS ×ᴳ Trunc-Group HS
Trunc-Group-× GS HS = group-ua
  (record {
    f = Trunc-rec (×-level Trunc-level Trunc-level)
          (λ {(a , b) → ([ a ] , [ b ])});
    pres-comp =
      Trunc-elim
        (λ _ → (Π-level (λ _ → =-preserves-level _
                                 (×-level Trunc-level Trunc-level))))
        (λ a → Trunc-elim
          (λ _ → =-preserves-level _ (×-level Trunc-level Trunc-level))
          (λ b → idp))} ,
   is-eq _
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

Trunc-Group-hom : ∀ {i j} {A : Type i} {B : Type j}
  {GS : GroupStructure A} {HS : GroupStructure B} (f : A → B)
  → ((a₁ a₂ : A) → f (GroupStructure.comp GS a₁ a₂)
                   == GroupStructure.comp HS (f a₁) (f a₂))
  → (Trunc-Group GS →ᴳ Trunc-Group HS)
Trunc-Group-hom {A = A} {GS = GS} {HS = HS} f p =
  record {f = Trunc-fmap f; pres-comp = pres-comp}
  where
  abstract
    pres-comp : (t₁ t₂ : Trunc ⟨0⟩ A) →
      Trunc-fmap f (Trunc-fmap2 (GroupStructure.comp GS) t₁ t₂)
      == Trunc-fmap2 (GroupStructure.comp HS)
           (Trunc-fmap f t₁) (Trunc-fmap f t₂)
    pres-comp =
      Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
        (λ a₁ → Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
          (λ a₂ → ap [_] (p a₁ a₂)))

Trunc-Group-iso : ∀ {i} {A B : Type i}
  {GS : GroupStructure A} {HS : GroupStructure B} (f : A → B)
  → ((a₁ a₂ : A) → f (GroupStructure.comp GS a₁ a₂)
                   == GroupStructure.comp HS (f a₁) (f a₂))
  → is-equiv f → Trunc-Group GS ≃ᴳ Trunc-Group HS
Trunc-Group-iso f pres-comp ie =
  (Trunc-Group-hom f pres-comp ,
   is-eq _ (Trunc-fmap (is-equiv.g ie))
     (Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
       (λ b → ap [_] (is-equiv.f-g ie b)))
     (Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
       (λ a → ap [_] (is-equiv.g-f ie a))))

Trunc-Group-abelian : ∀ {i} {A : Type i} (GS : GroupStructure A)
  → ((a₁ a₂ : A) → GroupStructure.comp GS a₁ a₂ == GroupStructure.comp GS a₂ a₁)
  → is-abelian (Trunc-Group GS)
Trunc-Group-abelian GS ab =
  Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)) $
    λ a₁ → Trunc-elim (λ _ → =-preserves-level _ Trunc-level) $
      λ a₂ → ap [_] (ab a₁ a₂)
