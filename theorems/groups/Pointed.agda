{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.Pointed where

⊙Group : (i : ULevel) → Type (lsucc i)
⊙Group i = Σ (Group i) Group.El

_⊙→ᴳ_ : {i j : ULevel} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙→ᴳ ⊙H = Σ (fst ⊙G →ᴳ fst ⊙H) (λ φ → GroupHom.f φ (snd ⊙G) == snd ⊙H)

_⊙≃ᴳ_ : {i j : ULevel} → ⊙Group i → ⊙Group j → Type (lmax i j)
⊙G ⊙≃ᴳ ⊙H = Σ (fst ⊙G ≃ᴳ fst ⊙H) (λ φ → GroupIso.f φ (snd ⊙G) == snd ⊙H)
