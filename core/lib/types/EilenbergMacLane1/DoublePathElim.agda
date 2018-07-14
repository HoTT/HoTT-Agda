{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.cubical.Square
open import lib.types.Group
open import lib.types.EilenbergMacLane1.Core
open import lib.types.EilenbergMacLane1.DoubleElim

module lib.types.EilenbergMacLane1.DoublePathElim where

private

  module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

    custom-square-over :
      {x y z : A} {p : x == y} {q : y == z} {r : x == z}
      (comp : r == p ∙ q)
      {u : f x == g x} {v : f y == g y} {w : f z == g z}
      (p-sq : Square u (ap f p) (ap g p) v)
      (q-sq : Square v (ap f q) (ap g q) w)
      (r-sq : Square u (ap f r) (ap g r) w)
      → r-sq ⊡v∙ ap (ap g) comp ==
        ap (ap f) comp ∙v⊡ ↓-='-square-comp p-sq q-sq
      → r-sq == ↓-='-square-comp p-sq q-sq
          [ (λ s → Square u (ap f s) (ap g s) w) ↓ comp ]
    custom-square-over {p = idp} {q = idp} {r = .idp} idp p-sq q-sq r-sq e = e

    embase-emloop-comp-helper :
      {x y z : A} {p : x == y} {q : y == z} {r : x == z}
      (comp : r == p ∙ q)
      {u : f x == g x} {v : f y == g y} {w : f z == g z}
      (p-sq : Square u (ap f p) (ap g p) v)
      (q-sq : Square v (ap f q) (ap g q) w)
      (r-sq : Square u (ap f r) (ap g r) w)
      → r-sq ⊡v∙ ap (ap g) comp ==
        ap (ap f) comp ∙v⊡ ↓-='-square-comp p-sq q-sq
      → ↓-='-from-square r-sq == ↓-='-from-square p-sq ∙ᵈ ↓-='-from-square q-sq
          [ (λ p → u == w [ (λ x → f x == g x) ↓ p ]) ↓ comp ]
    embase-emloop-comp-helper comp p-sq q-sq r-sq e =
      ap↓ ↓-='-from-square (custom-square-over comp p-sq q-sq r-sq e) ▹
      ↓-='-from-square-comp p-sq q-sq

  emloop-emloop-eq-helper : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
    (f g : A → B → C)
    {a₀ a₁ : A} (p : a₀ == a₁)
    {b₀ b₁ : B} (q : b₀ == b₁)
    {u₀₀ : f a₀ b₀ == g a₀ b₀}
    {u₀₁ : f a₀ b₁ == g a₀ b₁}
    {u₁₀ : f a₁ b₀ == g a₁ b₀}
    {u₁₁ : f a₁ b₁ == g a₁ b₁}
    (sq₀₋ : Square u₀₀ (ap (f a₀) q) (ap (g a₀) q) u₀₁)
    (sq₁₋ : Square u₁₀ (ap (f a₁) q) (ap (g a₁) q) u₁₁)
    (sq₋₀ : Square u₀₀ (ap (λ a → f a b₀) p) (ap (λ a → g a b₀) p) u₁₀)
    (sq₋₁ : Square u₀₁ (ap (λ a → f a b₁) p) (ap (λ a → g a b₁) p) u₁₁)
    → ap-comm f p q ∙v⊡ (sq₀₋ ⊡h sq₋₁)
      ==
      (sq₋₀ ⊡h sq₁₋) ⊡v∙ ap-comm g p q
    → ↓-ap-in (λ Z → Z) (λ a → f a b₀ == g a b₀) (↓-='-from-square sq₋₀) ∙'ᵈ
      ↓-ap-in (λ Z → Z) (λ b → f a₁ b == g a₁ b) (↓-='-from-square sq₁₋)
      ==
      ↓-ap-in (λ Z → Z) (λ b → f a₀ b == g a₀ b) (↓-='-from-square sq₀₋) ∙ᵈ
      ↓-ap-in (λ Z → Z) (λ a → f a b₁ == g a b₁) (↓-='-from-square sq₋₁)
        [ (λ p → u₀₀ == u₁₁ [ (λ Z → Z) ↓ p ]) ↓
          ap-comm' (λ a b → f a b == g a b) p q ]
  emloop-emloop-eq-helper f g idp idp sq₀₋ sq₁₋ sq₋₀ sq₋₁ r =
    horiz-degen-path sq₋₀ ∙' horiz-degen-path sq₁₋
      =⟨ ∙'=∙ (horiz-degen-path sq₋₀) (horiz-degen-path sq₁₋) ⟩
    horiz-degen-path sq₋₀ ∙ horiz-degen-path sq₁₋
      =⟨ ! (horiz-degen-path-⊡h sq₋₀ sq₁₋) ⟩
    horiz-degen-path (sq₋₀ ⊡h sq₁₋)
      =⟨ ap horiz-degen-path (! r) ⟩
    horiz-degen-path (sq₀₋ ⊡h sq₋₁)
      =⟨ horiz-degen-path-⊡h sq₀₋ sq₋₁ ⟩
    horiz-degen-path sq₀₋ ∙ horiz-degen-path sq₋₁ =∎

module _ {i j} (G : Group i) (H : Group j) where

  private
    module G = Group G
    module H = Group H

  module EM₁Level₂DoublePathElim {k} {C : Type k}
    {{C-level : has-level 2 C}}
    (f₁ f₂ : EM₁ G → EM₁ H → C)
    (embase-embase* : f₁ embase embase == f₂ embase embase)
    (embase-emloop* : ∀ h →
      Square embase-embase* (ap (f₁ embase) (emloop h))
             (ap (f₂ embase) (emloop h)) embase-embase*)
    (emloop-embase* : ∀ g →
      Square embase-embase* (ap (λ x → f₁ x embase) (emloop g))
             (ap (λ x → f₂ x embase) (emloop g)) embase-embase*)
    (embase-emloop-comp* : ∀ h₁ h₂ →
      embase-emloop* (H.comp h₁ h₂) ⊡v∙
      ap (ap (f₂ embase)) (emloop-comp' H h₁ h₂)
      ==
      ap (ap (f₁ embase)) (emloop-comp' H h₁ h₂) ∙v⊡
      ↓-='-square-comp (embase-emloop* h₁) (embase-emloop* h₂))
    (emloop-comp-embase* : ∀ g₁ g₂ →
      emloop-embase* (G.comp g₁ g₂) ⊡v∙
      ap (ap (λ x → f₂ x embase)) (emloop-comp' G g₁ g₂)
      ==
      ap (ap (λ x → f₁ x embase)) (emloop-comp' G g₁ g₂) ∙v⊡
      ↓-='-square-comp (emloop-embase* g₁) (emloop-embase* g₂))
    (emloop-emloop* : ∀ g h →
      ap-comm f₁ (emloop g) (emloop h) ∙v⊡
      (embase-emloop* h ⊡h emloop-embase* g)
      ==
      (emloop-embase* g ⊡h embase-emloop* h) ⊡v∙
      ap-comm f₂ (emloop g) (emloop h))
    where

    private
      module M =
        EM₁Level₁DoubleElim G H
          {P = λ x y → f₁ x y == f₂ x y}
          {{λ x y → has-level-apply C-level _ _}}
          embase-embase*
          (λ h → ↓-='-from-square (embase-emloop* h))
          (λ g → ↓-='-from-square (emloop-embase* g))
          (λ h₁ h₂ →
            embase-emloop-comp-helper (emloop-comp h₁ h₂)
                                      (embase-emloop* h₁)
                                      (embase-emloop* h₂)
                                      (embase-emloop* (H.comp h₁ h₂))
                                      (embase-emloop-comp* h₁ h₂))
          (λ g₁ g₂ →
            embase-emloop-comp-helper (emloop-comp g₁ g₂)
                                      (emloop-embase* g₁)
                                      (emloop-embase* g₂)
                                      (emloop-embase* (G.comp g₁ g₂))
                                      (emloop-comp-embase* g₁ g₂))
          (λ g h →
            emloop-emloop-eq-helper f₁ f₂
                                    (emloop g) (emloop h)
                                    (embase-emloop* h)
                                    (embase-emloop* h)
                                    (emloop-embase* g)
                                    (emloop-embase* g)
                                    (emloop-emloop* g h) )

    open M public
