{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.NType2
open import lib.types.EilenbergMacLane1.Core

module lib.types.EilenbergMacLane1.DoubleElim where

private

  emloop-emloop-helper : ∀ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k}
    {a : A} (p : a == a)
    {b₀ b₁ : B} (q : b₀ == b₁)
    (f : (b : B) → C a b)
    (g : (b : B) → C a b)
    (r₀ : f b₀ == g b₀ [ (λ a → C a b₀) ↓ p ])
    (r₁ : f b₁ == g b₁ [ (λ a → C a b₁) ↓ p ])
    → ↓-ap-in (λ Z → Z) (λ a → C a b₀) r₀ ∙'ᵈ ↓-ap-in (λ Z → Z) (C a) (apd g q) ==
      ↓-ap-in (λ Z → Z) (C a) (apd f q) ∙ᵈ ↓-ap-in (λ Z → Z) (λ a → C a b₁) r₁
        [ (λ p → f b₀ == g b₁ [ (λ Z → Z) ↓ p ]) ↓ ap-comm' C p q ]
    → r₀ == r₁ [ (λ b → f b == g b [ (λ a → C a b) ↓ p ]) ↓ q ]
  emloop-emloop-helper {C = C} p {b₀} idp f g r₀ r₁ s =
    –>-is-inj (↓-ap-equiv (λ Z → Z) (λ a → C a b₀)) r₀ r₁ $
    (! (▹idp (↓-ap-in (λ Z → Z) (λ a → C a b₀) r₀)) ∙
    s ∙
    idp◃ (↓-ap-in (λ Z → Z) (λ a → C a b₀) r₁))

module _ {i j} (G : Group i) (H : Group j) where

  private
    module G = Group G
    module H = Group H

  module EM₁Level₁DoubleElim {k} {P : EM₁ G → EM₁ H → Type k}
    {{P-level : ∀ x y → has-level 1 (P x y)}}
    (embase-embase* : P embase embase)
    (embase-emloop* : ∀ h → embase-embase* == embase-embase* [ P embase ↓ emloop h ])
    (emloop-embase* : ∀ g → embase-embase* == embase-embase* [ (λ x → P x embase) ↓ emloop g ])
    (embase-emloop-comp* : ∀ h₁ h₂ →
      embase-emloop* (H.comp h₁ h₂) == embase-emloop* h₁ ∙ᵈ embase-emloop* h₂
        [ (λ p → embase-embase* == embase-embase* [ P embase ↓ p ]) ↓ emloop-comp h₁ h₂ ])
    (emloop-comp-embase* : ∀ g₁ g₂ →
      emloop-embase* (G.comp g₁ g₂) == emloop-embase* g₁ ∙ᵈ emloop-embase* g₂
        [ (λ p → embase-embase* == embase-embase* [ (λ x → P x embase) ↓ p ]) ↓ emloop-comp g₁ g₂ ])
    (emloop-emloop* : ∀ g h →
      ↓-ap-in (λ Z → Z) (λ a → P a embase) (emloop-embase* g) ∙'ᵈ
      ↓-ap-in (λ Z → Z) (P embase) (embase-emloop* h)
      ==
      ↓-ap-in (λ Z → Z) (P embase) (embase-emloop* h) ∙ᵈ
      ↓-ap-in (λ Z → Z) (λ a → P a embase) (emloop-embase* g)
        [ (λ p → embase-embase* == embase-embase* [ (λ Z → Z) ↓ p ]) ↓ ap-comm' P (emloop g) (emloop h) ])
    where

    private
      module Embase =
        EM₁Level₁Elim {P = P embase}
                      {{P-level embase}}
                      embase-embase*
                      embase-emloop*
                      embase-emloop-comp*

      P' : embase' G == embase → EM₁ H → Type k
      P' p y = Embase.f y == Embase.f y [ (λ x → P x y) ↓ p ]

      P'-level : ∀ p y → has-level 0 (P' p y)
      P'-level _ y = ↓-level (P-level embase y)

      emloop-emloop** : ∀ g h → emloop-embase* g == emloop-embase* g [ P' (emloop g) ↓ emloop h ]
      emloop-emloop** g h =
        emloop-emloop-helper
          {C = P}
          (emloop g) (emloop h)
          Embase.f Embase.f
          (emloop-embase* g) (emloop-embase* g)
          (transport!
            (λ u →
              ↓-ap-in (λ Z → Z) (λ a → P a embase) (emloop-embase* g) ∙'ᵈ
              ↓-ap-in (λ Z → Z) (P embase) u
              ==
              ↓-ap-in (λ Z → Z) (P embase) u ∙ᵈ
              ↓-ap-in (λ Z → Z) (λ a → P a embase) (emloop-embase* g)
                [ (λ p → embase-embase* == embase-embase* [ (λ Z → Z) ↓ p ]) ↓ ap-comm' P (emloop g) (emloop h) ])
            (Embase.emloop-β h)
            (emloop-emloop* g h))

      module Emloop (g : G.El) =
        EM₁SetElim {P = P' (emloop g)}
                   {{P'-level (emloop g)}}
                   (emloop-embase* g)
                   (emloop-emloop** g)

      module EmloopComp (g₁ g₂ : G.El) =
        EM₁PropElim {P = λ y → Emloop.f (G.comp g₁ g₂) y ==
                               Emloop.f g₁ y ∙ᵈ Emloop.f g₂ y
                                 [ (λ x → P' x y) ↓ emloop-comp g₁ g₂ ]}
                    {{λ y → ↓-level (P'-level _ y)}}
                    (emloop-comp-embase* g₁ g₂)

      module DoubleElim (y : EM₁ H) =
        EM₁Level₁Elim {P = λ x → P x y}
                      {{λ x → P-level x y}}
                      (Embase.f y)
                      (λ g → Emloop.f g y)
                      (λ g₁ g₂ → EmloopComp.f g₁ g₂ y)

    abstract
      f : ∀ x y → P x y
      f x y = DoubleElim.f y x
