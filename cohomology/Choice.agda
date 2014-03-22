{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.Choice where

unchoose : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j}
  → Trunc n (Π A B) → Π A (Trunc n ∘ B)
unchoose = Trunc-rec (Π-level (λ _ → Trunc-level)) (λ f → [_] ∘ f)

has-choice : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : A → Type j) → Type (lmax i j)
has-choice {i} {j} n A B = is-equiv (unchoose {n = n} {A} {B})

{- Binary Choice -}
module _ {i} {n : ℕ₋₂} {A : Bool → Type i} where

  private
    pick : ∀ {j} {C : Bool → Type j} → (C true) → (C false) → Π Bool C
    pick x y true = x
    pick x y false = y

    pick-η : ∀ {j} {C : Bool → Type j} (f : Π Bool C)
      → pick (f true) (f false) == f
    pick-η {C = C} f = λ= lemma
      where
      lemma : (b : Bool) → pick {C = C} (f true) (f false) b == f b
      lemma true = idp
      lemma false = idp

    choose : Π Bool (Trunc n ∘ A) → Trunc n (Π Bool A)
    choose f = Trunc-rec Trunc-level
      (λ ft → Trunc-rec Trunc-level
        (λ ff → [ pick ft ff ] )
        (f false)) 
      (f true)

    unc-c : ∀ f → unchoose (choose f) == f
    unc-c f = transport (λ h → unchoose (choose h) == h) (pick-η f) $
      Trunc-elim
        {B = λ tft → 
          unchoose (choose (pick tft (f false))) == pick tft (f false)}
        (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
        (λ ft → Trunc-elim
          {B = λ tff → 
            unchoose (choose (pick [ ft ] tff )) == pick [ ft ] tff}
          (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
          (λ ff → ! (pick-η _))
          (f false))
        (f true)

    c-unc : ∀ tg → choose (unchoose tg) == tg
    c-unc = Trunc-elim
      {B = λ tg → choose (unchoose tg) == tg}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ g → ap [_] (pick-η g))

  Bool-has-choice : has-choice n Bool A
  Bool-has-choice = is-eq unchoose choose unc-c c-unc

