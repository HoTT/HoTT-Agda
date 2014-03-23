{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.Choice where

unchoose : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j}
  → Trunc n (Π A B) → Π A (Trunc n ∘ B)
unchoose = Trunc-rec (Π-level (λ _ → Trunc-level)) (λ f → [_] ∘ f)

has-choice : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : A → Type j) → Type (lmax i j)
has-choice {i} {j} n A B = is-equiv (unchoose {n = n} {A} {B})

{- Binary Choice -}
pick-Bool : ∀ {j} {C : Bool → Type j} → (C true) → (C false) → Π Bool C
pick-Bool x y true = x
pick-Bool x y false = y

pick-Bool-η : ∀ {j} {C : Bool → Type j} (f : Π Bool C)
  → pick-Bool (f true) (f false) == f
pick-Bool-η {C = C} f = λ= lemma
  where
  lemma : (b : Bool) → pick-Bool {C = C} (f true) (f false) b == f b
  lemma true = idp
  lemma false = idp

module _ {i} {n : ℕ₋₂} {A : Bool → Type i} where
  choose-Bool : Π Bool (Trunc n ∘ A) → Trunc n (Π Bool A)
  choose-Bool f = Trunc-rec Trunc-level
    (λ ft → Trunc-rec Trunc-level
      (λ ff → [ pick-Bool ft ff ] )
      (f false)) 
    (f true)

  choose-Bool-squash : (f : Π Bool A) 
    → choose-Bool (λ b → [ f b ]) == [ f ]
  choose-Bool-squash f = ap [_] (pick-Bool-η f)

  private
    unc-c : ∀ f → unchoose (choose-Bool f) == f
    unc-c f = transport (λ h → unchoose (choose-Bool h) == h) (pick-Bool-η f) $
      Trunc-elim
        {B = λ tft → 
          unchoose (choose-Bool (pick-Bool tft (f false))) 
          == pick-Bool tft (f false)}
        (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
        (λ ft → Trunc-elim
          {B = λ tff → 
            unchoose (choose-Bool (pick-Bool [ ft ] tff ))
            == pick-Bool [ ft ] tff}
          (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
          (λ ff → ! (pick-Bool-η _))
          (f false))
        (f true)

    c-unc : ∀ tg → choose-Bool (unchoose tg) == tg
    c-unc = Trunc-elim
      {B = λ tg → choose-Bool (unchoose tg) == tg}
      (λ _ → =-preserves-level _ Trunc-level)
      (λ g → ap [_] (pick-Bool-η g))

  Bool-has-choice : has-choice n Bool A
  Bool-has-choice = is-eq unchoose choose-Bool unc-c c-unc

