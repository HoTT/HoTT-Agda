{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.GroupProduct
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.TruncationGroup where

module _ {i} {El : Type i} (GS : GroupStructure El) where

  Trunc-group-struct : GroupStructure (Trunc 0 El)
  Trunc-group-struct = record {
    ident = [ ident GS ];
    inv = Trunc-fmap (inv GS);
    comp = _⊗_;
    unit-l = t-unit-l;
    assoc = t-assoc;
    inv-l = t-inv-l}
    where
    open GroupStructure
    infix 80 _⊗_
    _⊗_ = Trunc-fmap2 (comp GS)

    abstract
      t-unit-l : (t : Trunc 0 El) → [ ident GS ] ⊗ t == t
      t-unit-l = Trunc-elim (λ _ → =-preserves-level Trunc-level)
        (ap [_] ∘ unit-l GS)

      t-assoc : (t₁ t₂ t₃ : Trunc 0 El) → (t₁ ⊗ t₂) ⊗ t₃ == t₁ ⊗ (t₂ ⊗ t₃)
      t-assoc = Trunc-elim
        (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level Trunc-level)))
        (λ a → Trunc-elim
          (λ _ → Π-level (λ _ → =-preserves-level Trunc-level))
          (λ b → Trunc-elim
             (λ _ → =-preserves-level Trunc-level)
             (λ c → ap [_] (assoc GS a b c))))

      t-inv-l : (t : Trunc 0 El) → Trunc-fmap (inv GS) t ⊗ t == [ ident GS ]
      t-inv-l = Trunc-elim (λ _ → =-preserves-level Trunc-level)
        (ap [_] ∘ inv-l GS)


  Trunc-group : Group i
  Trunc-group = record {
    El = Trunc 0 El;
    El-level = Trunc-level;
    group-struct = Trunc-group-struct }

Trunc-group-× : ∀ {i j} {A : Type i} {B : Type j}
  (GS : GroupStructure A) (HS : GroupStructure B)
  → Trunc-group (×-group-struct GS HS) ≃ᴳ Trunc-group GS ×ᴳ Trunc-group HS
Trunc-group-× GS HS =
  group-hom (fanout (Trunc-fmap fst) (Trunc-fmap snd))
    (Trunc-elim
      (λ _ → (Π-level (λ _ → =-preserves-level
                               (×-level Trunc-level Trunc-level))))
      (λ a → Trunc-elim
        (λ _ → =-preserves-level (×-level Trunc-level Trunc-level))
        (λ b → idp))) ,
  is-eq _
    (uncurry (Trunc-fmap2 _,_))
    (uncurry (Trunc-elim
               (λ _ → Π-level (λ _ → =-preserves-level
                                       (×-level Trunc-level Trunc-level)))
               (λ a → Trunc-elim
                        (λ _ → =-preserves-level
                                 (×-level Trunc-level Trunc-level))
                        (λ b → idp))))
    (Trunc-elim (λ _ → =-preserves-level Trunc-level) (λ _ → idp))

Trunc-group-fmap : ∀ {i j} {A : Type i} {B : Type j}
  {GS : GroupStructure A} {HS : GroupStructure B}
  → (GS →ᴳˢ HS) → (Trunc-group GS →ᴳ Trunc-group HS)
Trunc-group-fmap {A = A} {GS = GS} {HS = HS} (group-structure-hom f p) =
  group-hom (Trunc-fmap f) pres-comp
  where
  abstract
    pres-comp : (t₁ t₂ : Trunc 0 A) →
      Trunc-fmap f (Trunc-fmap2 (GroupStructure.comp GS) t₁ t₂)
      == Trunc-fmap2 (GroupStructure.comp HS)
           (Trunc-fmap f t₁) (Trunc-fmap f t₂)
    pres-comp =
      Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level Trunc-level))
        (λ a₁ → Trunc-elim (λ _ → =-preserves-level Trunc-level)
          (λ a₂ → ap [_] (p a₁ a₂)))

Trunc-group-emap : ∀ {i j} {A : Type i} {B : Type j}
  {GS : GroupStructure A} {HS : GroupStructure B}
  → GS ≃ᴳˢ HS → Trunc-group GS ≃ᴳ Trunc-group HS
Trunc-group-emap (φ , ie) =
  (Trunc-group-fmap φ ,
   is-eq _ (Trunc-fmap (is-equiv.g ie))
     (Trunc-elim (λ _ → =-preserves-level Trunc-level)
       (λ b → ap [_] (is-equiv.f-g ie b)))
     (Trunc-elim (λ _ → =-preserves-level Trunc-level)
       (λ a → ap [_] (is-equiv.g-f ie a))))

Trunc-group-abelian : ∀ {i} {A : Type i} (GS : GroupStructure A)
  → ((a₁ a₂ : A) → GroupStructure.comp GS a₁ a₂ == GroupStructure.comp GS a₂ a₁)
  → is-abelian (Trunc-group GS)
Trunc-group-abelian GS ab =
  Trunc-elim (λ _ → Π-level (λ _ → =-preserves-level Trunc-level)) $
    λ a₁ → Trunc-elim (λ _ → =-preserves-level Trunc-level) $
      λ a₂ → ap [_] (ab a₁ a₂)

unTrunc-iso : ∀ {i} {A : Type i} (GS : GroupStructure A)
  → (A-is-set : is-set A) → Trunc-group GS ≃ᴳ group A A-is-set GS
unTrunc-iso _ A-is-set = ≃-to-≃ᴳ (unTrunc-equiv _ A-is-set)
  (Trunc-elim (λ _ → Π-is-set λ _ → =-preserves-set A-is-set)
    (λ a₁ → Trunc-elim (λ _ → =-preserves-set A-is-set)
      (λ a₂ → idp)))
