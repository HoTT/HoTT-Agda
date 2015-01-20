{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.3x3.PushoutPushout where

-- Numbering is in row/column form
-- A span^2 is a 5 × 5 table (numbered from 0 to 4) where
-- * the even/even cells are types
-- * the odd/even and even/odd cells are functions
-- * the odd/odd cells are equalities between functions
record Span^2 {i} : Type (lsucc i) where
  constructor span^2
  field
    A₀₀ A₀₂ A₀₄ A₂₀ A₂₂ A₂₄ A₄₀ A₄₂ A₄₄ : Type i
    f₀₁ : A₀₂ → A₀₀
    f₀₃ : A₀₂ → A₀₄
    f₂₁ : A₂₂ → A₂₀
    f₂₃ : A₂₂ → A₂₄
    f₄₁ : A₄₂ → A₄₀
    f₄₃ : A₄₂ → A₄₄
    f₁₀ : A₂₀ → A₀₀
    f₃₀ : A₂₀ → A₄₀
    f₁₂ : A₂₂ → A₀₂
    f₃₂ : A₂₂ → A₄₂
    f₁₄ : A₂₄ → A₀₄
    f₃₄ : A₂₄ → A₄₄
    H₁₁ : (x : A₂₂) → f₁₀ (f₂₁ x) == f₀₁ (f₁₂ x)
    H₁₃ : (x : A₂₂) → f₀₃ (f₁₂ x) == f₁₄ (f₂₃ x)
    H₃₁ : (x : A₂₂) → f₃₀ (f₂₁ x) == f₄₁ (f₃₂ x)
    H₃₃ : (x : A₂₂) → f₄₃ (f₃₂ x) == f₃₄ (f₂₃ x)

record SquareFunc {i} : Type (lsucc i) where
  constructor square
  field
    {A B₁ B₂ C} : Type i
    f₁ : A  → B₁
    f₂ : A  → B₂
    g₁ : B₁ → C
    g₂ : B₂ → C

module _ {i} where

  square=-raw :
    {A A' : Type i} (eq-A : A == A')
    {B₁ B₁' : Type i} (eq-B₁ : B₁ == B₁')
    {B₂ B₂' : Type i} (eq-B₂ : B₂ == B₂')
    {C C' : Type i} (eq-C : C == C')
    {f₁ : A → B₁} {f₁' : A' → B₁'} (eq-f₁ : f₁ == f₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A eq-B₁ ])
    {f₂ : A → B₂} {f₂' : A' → B₂'} (eq-f₂ : f₂ == f₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A eq-B₂ ])
    {g₁ : B₁ → C} {g₁' : B₁' → C'} (eq-g₁ : g₁ == g₁' [ (λ u → fst u → snd u) ↓ pair×= eq-B₁ eq-C ])
    {g₂ : B₂ → C} {g₂' : B₂' → C'} (eq-g₂ : g₂ == g₂' [ (λ u → fst u → snd u) ↓ pair×= eq-B₂ eq-C ])
    → square f₁ f₂ g₁ g₂ == square f₁' f₂' g₁' g₂'
  square=-raw idp idp idp idp idp idp idp idp = idp

  square-thing :
    {A A' : Type i} (eq-A : A == A')
    {B₁ B₁' : Type i} (eq-B₁ : B₁ == B₁')
    {B₂ B₂' : Type i} (eq-B₂ : B₂ == B₂')
    {C C' : Type i} (eq-C : C == C')
    {f₁ : A → B₁} {f₁' : A' → B₁'} (eq-f₁ : f₁ == f₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A eq-B₁ ])
    {f₂ : A → B₂} {f₂' : A' → B₂'} (eq-f₂ : f₂ == f₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A eq-B₂ ])
    {g₁ : B₁ → C} {g₁' : B₁' → C'} (eq-g₁ : g₁ == g₁' [ (λ u → fst u → snd u) ↓ pair×= eq-B₁ eq-C ])
    {g₂ : B₂ → C} {g₂' : B₂' → C'} (eq-g₂ : g₂ == g₂' [ (λ u → fst u → snd u) ↓ pair×= eq-B₂ eq-C ])
    {a : _} {b : _}
    → a == b [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₂ u (SquareFunc.f₂ u x) == SquareFunc.g₁ u (SquareFunc.f₁ u x))) ↓ (square=-raw eq-A eq-B₂ eq-B₁ eq-C eq-f₂ eq-f₁ eq-g₂ eq-g₁) ]
    → a == b [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x))) ↓ (square=-raw eq-A eq-B₁ eq-B₂ eq-C eq-f₁ eq-f₂ eq-g₁ eq-g₂) ]
  square-thing idp idp idp idp idp idp idp idp α = α

  span^2=-raw :
    {A₀₀ A₀₀' : Type i} (eq-A₀₀ : A₀₀ == A₀₀')
    {A₀₂ A₀₂' : Type i} (eq-A₀₂ : A₀₂ == A₀₂')
    {A₀₄ A₀₄' : Type i} (eq-A₀₄ : A₀₄ == A₀₄')
    {A₂₀ A₂₀' : Type i} (eq-A₂₀ : A₂₀ == A₂₀')
    {A₂₂ A₂₂' : Type i} (eq-A₂₂ : A₂₂ == A₂₂')
    {A₂₄ A₂₄' : Type i} (eq-A₂₄ : A₂₄ == A₂₄')
    {A₄₀ A₄₀' : Type i} (eq-A₄₀ : A₄₀ == A₄₀')
    {A₄₂ A₄₂' : Type i} (eq-A₄₂ : A₄₂ == A₄₂')
    {A₄₄ A₄₄' : Type i} (eq-A₄₄ : A₄₄ == A₄₄')
    {f₀₁ : A₀₂ → A₀₀} {f₀₁' : A₀₂' → A₀₀'} (eq-f₀₁ : f₀₁ == f₀₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₀₂ eq-A₀₀ ])
    {f₀₃ : A₀₂ → A₀₄} {f₀₃' : A₀₂' → A₀₄'} (eq-f₀₃ : f₀₃ == f₀₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₀₂ eq-A₀₄ ])
    {f₂₁ : A₂₂ → A₂₀} {f₂₁' : A₂₂' → A₂₀'} (eq-f₂₁ : f₂₁ == f₂₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₂₀ ])
    {f₂₃ : A₂₂ → A₂₄} {f₂₃' : A₂₂' → A₂₄'} (eq-f₂₃ : f₂₃ == f₂₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₂₄ ])
    {f₄₁ : A₄₂ → A₄₀} {f₄₁' : A₄₂' → A₄₀'} (eq-f₄₁ : f₄₁ == f₄₁' [ (λ u → fst u → snd u) ↓ pair×= eq-A₄₂ eq-A₄₀ ])
    {f₄₃ : A₄₂ → A₄₄} {f₄₃' : A₄₂' → A₄₄'} (eq-f₄₃ : f₄₃ == f₄₃' [ (λ u → fst u → snd u) ↓ pair×= eq-A₄₂ eq-A₄₄ ])
    {f₁₀ : A₂₀ → A₀₀} {f₁₀' : A₂₀' → A₀₀'} (eq-f₁₀ : f₁₀ == f₁₀' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₀ eq-A₀₀ ])
    {f₃₀ : A₂₀ → A₄₀} {f₃₀' : A₂₀' → A₄₀'} (eq-f₃₀ : f₃₀ == f₃₀' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₀ eq-A₄₀ ])
    {f₁₂ : A₂₂ → A₀₂} {f₁₂' : A₂₂' → A₀₂'} (eq-f₁₂ : f₁₂ == f₁₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₀₂ ])
    {f₃₂ : A₂₂ → A₄₂} {f₃₂' : A₂₂' → A₄₂'} (eq-f₃₂ : f₃₂ == f₃₂' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₂ eq-A₄₂ ])
    {f₁₄ : A₂₄ → A₀₄} {f₁₄' : A₂₄' → A₀₄'} (eq-f₁₄ : f₁₄ == f₁₄' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₄ eq-A₀₄ ])
    {f₃₄ : A₂₄ → A₄₄} {f₃₄' : A₂₄' → A₄₄'} (eq-f₃₄ : f₃₄ == f₃₄' [ (λ u → fst u → snd u) ↓ pair×= eq-A₂₄ eq-A₄₄ ])
    {H₁₁ : (x : A₂₂) → f₁₀ (f₂₁ x) == f₀₁ (f₁₂ x)} {H₁₁' : (x : A₂₂') → f₁₀' (f₂₁' x) == f₀₁' (f₁₂' x)}
    (eq-H₁₁ : H₁₁ == H₁₁' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                          ↓ square=-raw eq-A₂₂ eq-A₂₀ eq-A₀₂ eq-A₀₀ eq-f₂₁ eq-f₁₂ eq-f₁₀ eq-f₀₁ ])
    {H₁₃ : (x : A₂₂) → f₀₃ (f₁₂ x) == f₁₄ (f₂₃ x)} {H₁₃' : (x : A₂₂') → f₀₃' (f₁₂' x) == f₁₄' (f₂₃' x)}
    (eq-H₁₃ : H₁₃ == H₁₃' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                          ↓ square=-raw eq-A₂₂ eq-A₀₂ eq-A₂₄ eq-A₀₄ eq-f₁₂ eq-f₂₃ eq-f₀₃ eq-f₁₄ ])
    {H₃₁ : (x : A₂₂) → f₃₀ (f₂₁ x) == f₄₁ (f₃₂ x)} {H₃₁' : (x : A₂₂') → f₃₀' (f₂₁' x) == f₄₁' (f₃₂' x)}
    (eq-H₃₁ : H₃₁ == H₃₁' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                          ↓ square=-raw eq-A₂₂ eq-A₂₀ eq-A₄₂ eq-A₄₀ eq-f₂₁ eq-f₃₂ eq-f₃₀ eq-f₄₁ ])
    {H₃₃ : (x : A₂₂) → f₄₃ (f₃₂ x) == f₃₄ (f₂₃ x)} {H₃₃' : (x : A₂₂') → f₄₃' (f₃₂' x) == f₃₄' (f₂₃' x)}
    (eq-H₃₃ : H₃₃ == H₃₃' [ (λ u → ((x : SquareFunc.A u) → SquareFunc.g₁ u (SquareFunc.f₁ u x) == SquareFunc.g₂ u (SquareFunc.f₂ u x)))
                          ↓ square=-raw eq-A₂₂ eq-A₄₂ eq-A₂₄ eq-A₄₄ eq-f₃₂ eq-f₂₃ eq-f₄₃ eq-f₃₄ ])
     → span^2 A₀₀  A₀₂  A₀₄  A₂₀  A₂₂  A₂₄  A₄₀  A₄₂  A₄₄  f₀₁  f₀₃  f₂₁  f₂₃  f₄₁  f₄₃  f₁₀  f₃₀  f₁₂  f₃₂  f₁₄  f₃₄  H₁₁  H₁₃  H₃₁  H₃₃
    == span^2 A₀₀' A₀₂' A₀₄' A₂₀' A₂₂' A₂₄' A₄₀' A₄₂' A₄₄' f₀₁' f₀₃' f₂₁' f₂₃' f₄₁' f₄₃' f₁₀' f₃₀' f₁₂' f₃₂' f₁₄' f₃₄' H₁₁' H₁₃' H₃₁' H₃₃'
  span^2=-raw idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp idp = idp

module M {i} (d : Span^2 {i}) where

  open Span^2 d

  A₀∙ : Type i
  A₀∙ = Pushout (span A₀₀ A₀₄ A₀₂ f₀₁ f₀₃)

  A₂∙ : Type i
  A₂∙ = Pushout (span A₂₀ A₂₄ A₂₂ f₂₁ f₂₃)

  A₄∙ : Type i
  A₄∙ = Pushout (span A₄₀ A₄₄ A₄₂ f₄₁ f₄₃)

  module F₁∙ = PushoutRec {D = A₀∙}
                          (left ∘ f₁₀) (right ∘ f₁₄)
                          (λ c → ap left (H₁₁ c)
                                 ∙ glue (f₁₂ c)
                                 ∙ ap right (H₁₃ c))

  f₁∙ : A₂∙ → A₀∙
  f₁∙ = F₁∙.f

  module F₃∙ = PushoutRec {D = A₄∙}
                          (left ∘ f₃₀) (right ∘ f₃₄)
                          (λ c → ap left (H₃₁ c)
                                 ∙ glue (f₃₂ c)
                                 ∙ ap right (H₃₃ c))

  f₃∙ : A₂∙ → A₄∙
  f₃∙ = F₃∙.f

  -- Span obtained after taking horizontal pushouts
  v-h-span : Span
  v-h-span = span A₀∙ A₄∙ A₂∙ f₁∙ f₃∙

  Pushout^2 : Type i
  Pushout^2 = Pushout v-h-span

  {-
  Definition of [f₁∙] and [f₃∙] in ∞TT:

  f₁∙ : A₂∙ → A₀∙
  f₁∙ (left a) = left (f₁₀ a)
  f₁∙ (right c) = right (f₁₄ c)
  ap f₁∙ (glue b) = ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c)

  f₃∙ : A₂∙ → A₄∙
  f₃∙ (left a) = left (f₃₀ a)
  f₃∙ (right c) = right (f₃₄ c)
  ap f₃∙ (glue b) = ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c)
  -}
