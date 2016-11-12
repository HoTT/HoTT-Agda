{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module cohomology.Choice where

{- Binary Choice -}
module _ {k} where

  pick-Bool : ∀ {j} {C : Lift {j = k} Bool → Type j}
    → (C (lift true)) → (C (lift false)) → Π (Lift Bool) C
  pick-Bool x y (lift true) = x
  pick-Bool x y (lift false) = y

  pick-Bool-η : ∀ {j} {C : Lift Bool → Type j} (f : Π (Lift Bool) C)
    → pick-Bool (f (lift true)) (f (lift false)) == f
  pick-Bool-η {C = C} f = λ= lemma
    where
    lemma : (b : Lift Bool) →
      pick-Bool {C = C} (f (lift true)) (f (lift false)) b == f b
    lemma (lift true) = idp
    lemma (lift false) = idp

  module _ {i} {n : ℕ₋₂} {A : Lift {j = k} Bool → Type i} where
    choose-Bool : Π (Lift Bool) (Trunc n ∘ A) → Trunc n (Π (Lift Bool) A)
    choose-Bool f = Trunc-rec Trunc-level
      (λ ft → Trunc-rec Trunc-level
        (λ ff → [ pick-Bool ft ff ] )
        (f (lift false)))
      (f (lift true))

    choose-Bool-squash : (f : Π (Lift Bool) A)
      → choose-Bool (λ b → [ f b ]) == [ f ]
    choose-Bool-squash f = ap [_] (pick-Bool-η f)

    private
      unc-c : ∀ f → unchoose (choose-Bool f) == f
      unc-c f = transport
        (λ h → unchoose (choose-Bool h) == h)
        (pick-Bool-η f)
        (Trunc-elim
           {P = λ tft →
             unchoose (choose-Bool (pick-Bool tft (f (lift false))))
             == pick-Bool tft (f (lift false))}
           (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
           (λ ft → Trunc-elim
             {P = λ tff →
               unchoose (choose-Bool (pick-Bool [ ft ] tff ))
               == pick-Bool [ ft ] tff}
             (λ _ → =-preserves-level _ (Π-level (λ _ → Trunc-level)))
             (λ ff → ! (pick-Bool-η _))
             (f (lift false)))
           (f (lift true)))

      c-unc : ∀ tg → choose-Bool (unchoose tg) == tg
      c-unc = Trunc-elim
        {P = λ tg → choose-Bool (unchoose tg) == tg}
        (λ _ → =-preserves-level _ Trunc-level)
        (λ g → ap [_] (pick-Bool-η g))

    Bool-has-choice : ∀ j → has-choice n (Lift Bool) A
    Bool-has-choice = is-eq unchoose choose-Bool unc-c c-unc

