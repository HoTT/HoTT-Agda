{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.Pointed where

infix 60 ⊙[_,_]ᴳ

record ⊙Group (i : ULevel) : Type (lsucc i) where
  constructor ⊙[_,_]ᴳ
  field
    de⊙ᴳ : Group i
    ptᴳ : Group.El de⊙ᴳ
open ⊙Group

⊙Group₀ = ⊙Group lzero

_⊙→ᴳ_ : ∀ {i j} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙→ᴳ ⊙H = Σ (de⊙ᴳ ⊙G →ᴳ de⊙ᴳ ⊙H) (λ φ → GroupHom.f φ (ptᴳ ⊙G) == ptᴳ ⊙H)

_⊙≃ᴳ_ : ∀ {i j} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙≃ᴳ ⊙H = Σ (de⊙ᴳ ⊙G ≃ᴳ de⊙ᴳ ⊙H) (λ φ → GroupIso.f φ (ptᴳ ⊙G) == ptᴳ ⊙H)

is-infinite-cyclic : ∀ {i} → ⊙Group i → Type i
is-infinite-cyclic ⊙[ G , g ]ᴳ = is-equiv (Group.exp G g)
