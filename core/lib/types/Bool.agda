{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Bool where

{-
data Bool : Type₀ where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}
-}

Bool = ⊤ ⊔ ⊤

pattern true = inl unit
pattern false = inr unit

⊙Bool : Ptd₀
⊙Bool = ⊙[ Bool , true ]

Bool-elim : ∀ {i} {P : Bool → Type i} → P true → P false → Π Bool P
Bool-elim true* false* true = true*
Bool-elim true* false* false = false*

Bool-rec : ∀ {i} {A : Type i} → A → A → (Bool → A)
Bool-rec {A = A} = Bool-elim {P = λ _ → A}

negate : Bool → Bool
negate true = false
negate false = true

and : Bool → Bool → Bool
and true b = b
and false _ = false

xor : Bool → Bool → Bool
xor true = negate
xor false = idf Bool

xor-diag : ∀ (b : Bool) → xor b b == false
xor-diag true  = idp
xor-diag false = idp

and-false-r : ∀ b → and b false == false
and-false-r true = idp
and-false-r false = idp

and-comm : ∀ b c → and b c == and c b
and-comm false false = idp
and-comm false true = idp
and-comm true false = idp
and-comm true true = idp

private
  Bool-true≠false-type : Bool → Type₀
  Bool-true≠false-type true  = Unit
  Bool-true≠false-type false = Empty

abstract
  Bool-true≠false : true ≠ false
  Bool-true≠false p = transport Bool-true≠false-type p unit

  Bool-false≠true : false ≠ true
  Bool-false≠true p = transport Bool-true≠false-type (! p) unit

  Bool-has-dec-eq : has-dec-eq Bool
  Bool-has-dec-eq true true = inl idp
  Bool-has-dec-eq true false = inr Bool-true≠false
  Bool-has-dec-eq false true = inr Bool-false≠true
  Bool-has-dec-eq false false = inl idp

  Bool-is-set : is-set Bool
  Bool-is-set = dec-eq-is-set Bool-has-dec-eq

instance
  Bool-level : {n : ℕ₋₂} → has-level (S (S n)) Bool
  Bool-level = set-has-level-SS Bool-is-set
