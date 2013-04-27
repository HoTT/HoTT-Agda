{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.BlakersMassey.CoherenceData
  {i} {X Y : Set i} (Q : X → Y → Set i)
  {m} (Q-is-conn-x : ∀ x → is-connected (S m) (Σ Y (λ y → Q x y)))
  {n} (Q-is-conn-y : ∀ y → is-connected (S n) (Σ X (λ x → Q x y)))
  where

  open import Homotopy.PointConnected
  open import Homotopy.Truncation
  open import Homotopy.Extensions.ProductPushoutToProductToConnected
  open import Homotopy.BlakersMassey.PushoutWrapper Q

  glue-!glue : ∀ {x₀} {x₁} {y₀} (q₀₀ : Q x₀ y₀) (q₁₀ : Q x₁ y₀)
    → left x₀ ≡ left x₁
  glue-!glue q₀₀ q₁₀ = glue q₀₀ ∘ ! (glue q₁₀)

  glue-!glue-path : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) → glue-!glue q₀ q₀ ≡ glue-!glue q₁ q₁
  glue-!glue-path q₀ q₁ = opposite-right-inverse (glue q₀) ∘ ! (opposite-right-inverse (glue q₁))

  glue-!glue-path-glue : ∀ {x} {y} (q : Q x y) → refl ≡ glue-!glue-path q q
  glue-!glue-path-glue q = ! $ opposite-right-inverse (opposite-right-inverse (glue q))

  module _ {x₀} {y₁} (q₀₁ : Q x₀ y₁) r₀₁ (shift : glue q₀₁ ≡ r₀₁) where
    cross-path-template : ∀ {x₁} {y₀} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) (q₁₀ : Q x₁ y₀)
      → glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁
      → glue-!glue q₀₀ q₁₀ ≡ r₀₁ ∘ ! (glue q₁₁)
    cross-path-template q₀₀ q₁₁ q₁₀ path = path ∘ whisker-right (! (glue q₁₁)) shift

    cross-template : ∀ {x₁} {y₀} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) (q₁₀ : Q x₁ y₀)
      → glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁
      → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))
    cross-template q₀₀ q₁₁ q₁₀ path = proj (q₁₀ , cross-path-template q₀₀ q₁₁ q₁₀ path)

    cross′-left : ∀ {x₁} (q₁₁ : Q x₁ y₁)
      → τ (n +2+ m) (hfiber (glue-!glue q₀₁) (r₀₁ ∘ ! (glue q₁₁)))
    cross′-left q₁₁ = cross-template q₀₁ q₁₁ q₁₁ refl

    cross′-right : ∀ {y₀} (q₀₀ : Q x₀ y₀)
      → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₀₁)))
    cross′-right q₀₀ = cross-template q₀₀ q₀₁ q₀₀ (glue-!glue-path q₀₀ q₀₁)

    cross′-glue : cross′-left {x₀} q₀₁ ≡ cross′-right {y₁} q₀₁
    cross′-glue = ap (cross-template q₀₁ q₀₁ q₀₁) (glue-!glue-path-glue q₀₁)

    module Cross′ where

      open import Homotopy.Extensions.ProductPushoutToProductToConnected
        (point (Σ X λ x → Q x  y₁) (x₀ , q₀₁))
        (point (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁))
        (λ{(x₁ , q₁₁) (y₀ , q₀₀)
            → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))})
        {n} {m}
        ⦃ λ _ _ → τ-is-truncated (n +2+ m) _ ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₁) (x₀ , q₀₁) (Q-is-conn-y y₁))
        (point-has-connected-fibers (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁) (Q-is-conn-x x₀))
        (λ{(x₁ , q₁₁) _ → cross′-left q₁₁})
        (λ{_ (y₀ , q₀₀) → cross′-right q₀₀})
        (λ _ _ → cross′-glue)
        public

  abstract
    cross′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
      → hfiber glue r₀₁
      → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))
    cross′ q₀₀ q₁₁ r (q₀₁ , shift) =
      Cross′.connected-extend q₀₁ r shift (_ , q₁₁) (_ , q₀₀)

    cross′-β-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r₀ shift
      → cross′ q₀ q₁ r₀ (q₀ , shift)
      ≡ cross′-left q₀ r₀ shift q₁
    cross′-β-left q₀ q₁ r₀₁ shift =
      Cross′.connected-extend-β-left q₀ r₀₁ shift (_ , q₁) tt

    cross′-β-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r₁ shift
      → cross′ q₀ q₁ r₁ (q₁ , shift)
      ≡ cross′-right q₁ r₁ shift q₀
    cross′-β-right q₀ q₁ r₀₁ shift =
      Cross′.connected-extend-β-right q₁ r₀₁ shift tt (_ , q₀)

    cross′-triangle : ∀ {x} {y} (q : Q x y) r shift
      → cross′-β-left q q r shift
      ∘ cross′-glue q r shift
      ≡ cross′-β-right q q r shift
    cross′-triangle q r shift =
      Cross′.connected-extend-triangle q r shift tt tt

  cross : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (hfiber glue r₀₁) -- q₀₁ , path
    → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁))) -- q₁₀ , path
  cross q₀₀ q₁₁ r₀₁ = τ-extend-nondep ⦃ τ-is-truncated _ _ ⦄ (cross′ q₀₀ q₁₁ r₀₁)

{-
  -- TODO Integrate Dan's idea on proving the equivalence.

  cross-back′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁)
    (r : left x₀ ≡ right y₁) (q₁₀ : Q x₁ y₀)
    (shift : glue-!glue q₀₀ q₁₀ ≡ r ∘ ! (glue q₁₁))
    → τ (n +2+ m) (hfiber glue r)
  cross-back q₀₀ q₁₁ r₀₁ q₀₁ shift = τ-extend-nondep
    ⦃ τ-is-truncated (n +2+ m) _ ⦄
    (λ{(q₀₁ , shift′) →  })
    Cross′.connected-extend q₁₀ (_ , q₁₁) (_ , q₀₀) -- 0's and 1's swapped!
    -- gives τ (n +2+ m) (hfiber (glue-!glue q) (glue q ∘ ! (glue q′)))})

      cross-back″ x1 x2 q = transport (Trunc 2n o HFiber mer) q (Codes-mer' x1 x2)

    cross-back′ : ∀ (r₀₁ : left x₀ ≡ right y₀)
      → hfiber (glue-!glue q₀₁) (r₀₁ ∘ ! (glue q₀₁))
      → τ (n +2+ m) (hfiber glue r₀₁)

  cross-back0′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁))
    → τ (n +2+ m) (hfiber glue r₀₁)
  cross-back0′ q₀₀ q₁₁ r₀₁ q₁₀ path =
      Cross′.connected-extend q₀₁ (_ , q₁₁) (_ , q₀₀)
-}

  private
    module _ {x₁} {y₀} (q₁₀ : Q x₁ y₀) where
      return-path-template : ∀ {x₀} (q₀₀ : Q x₀ y₀) {y₁} (q₁₁ : Q x₁ y₁)
        r₀₁ (shift : glue-!glue q₀₀ q₁₀ ≡ r₀₁ ∘ ! (glue q₁₁)) (q₀₁ : Q x₀ y₁)
        → glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁
        → glue q₀₁ ≡ r₀₁
      return-path-template q₀₀ q₁₁ r₀₁ shift q₀₁ path =
        anti-whisker-right (! (glue q₁₁)) (! path ∘ shift)

      return-template : ∀ {x₀} (q₀₀ : Q x₀ y₀) {y₁} (q₁₁ : Q x₁ y₁)
        r₀₁ (shift : glue-!glue q₀₀ q₁₀ ≡ r₀₁ ∘ ! (glue q₁₁)) (q₀₁ : Q x₀ y₁)
        → glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁
        → τ (n +2+ m) (hfiber glue r₀₁)
      return-template q₀₀ q₁₁ r₀₁ shift q₀₁ path =
        proj (q₀₁ , return-path-template q₀₀ q₁₁ r₀₁ shift q₀₁ path)

      return′-left : ∀ {x₀} (q₀₀ : Q x₀ y₀)
        r₀₀ (shift : glue-!glue q₀₀ q₁₀ ≡ r₀₀ ∘ ! (glue q₁₀))
        → τ (n +2+ m) (hfiber glue r₀₀)
      return′-left q₀₀ r₀₀ shift = return-template q₀₀ q₁₀ r₀₀ shift q₀₀ refl

      return′-right : ∀ {y₁} (q₁₁ : Q x₁ y₁)
        r₁₁ (shift : glue q₁₀ ∘ ! (glue q₁₀) ≡ r₁₁ ∘ ! (glue q₁₁))
        → τ (n +2+ m) (hfiber glue r₁₁)
      return′-right q₁₁ r₁₁ shift =
        return-template q₁₀ q₁₁ r₁₁ shift q₁₁ (glue-!glue-path q₁₀ q₁₁)

      return′-glue : ∀ r₀₁ shift
        → return′-left q₁₀ r₀₁ shift ≡ return′-right q₁₀ r₀₁ shift
      return′-glue r₀₁ shift = ap (return-template q₁₀ q₁₀ r₀₁ shift q₁₀) (glue-!glue-path-glue q₁₀)

      return′-glue′ : return′-left q₁₀ ≡ return′-right q₁₀
      return′-glue′ = funext λ r₀₁ → funext λ shift → return′-glue r₀₁ shift

      module Return′ where
        open import Homotopy.Extensions.ProductPushoutToProductToConnected
          (point (Σ X λ x → Q x  y₀) (x₁ , q₁₀))
          (point (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀))
          (λ{(x₀ , q₀₀) (y₁ , q₁₁) → ∀ r₀₁ (shift : glue-!glue q₀₀ q₁₀ ≡ r₀₁ ∘ ! (glue q₁₁))
              → τ (n +2+ m) (hfiber glue r₀₁)})
          {n} {m}
          ⦃ λ _ _ → Π-is-truncated (n +2+ m)
              λ _ → →-is-truncated (n +2+ m)
                  $ τ-is-truncated (n +2+ m) _ ⦄
          (point-has-connected-fibers (Σ X λ x → Q x  y₀) (x₁ , q₁₀) (Q-is-conn-y y₀))
          (point-has-connected-fibers (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀) (Q-is-conn-x x₁))
          (λ{(x₀ , q₀₀) _ → return′-left q₀₀})
          (λ{_ (y₁ , q₁₁) → return′-right q₁₁})
          (λ _ _ → return′-glue′)
          public

  abstract
    return′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
      → hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁))
      → τ (n +2+ m) (hfiber glue r₀₁)
    return′ {x₀}{x₁} {y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₁₀ , shift) =
      Return′.connected-extend q₁₀ (x₀ , q₀₀) (y₁ , q₁₁) r₀₁ shift

    return′-β-left′ : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y)
      → (λ r₀ shift → return′ q₀ q₁ r₀ (q₁ , shift))
      ≡ return′-left q₁ q₀
    return′-β-left′ {x₀} q₀ q₁ =
      Return′.connected-extend-β-left q₁ (x₀ , q₀) tt

    return′-β-right′ : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁)
      → (λ r₁ shift → return′ q₀ q₁ r₁ (q₀ , shift))
      ≡ return′-right q₀ q₁
    return′-β-right′ {y₁ = y₁} q₀ q₁ =
      Return′.connected-extend-β-right q₀ tt (y₁ , q₁)

    return′-triangle′ : ∀ {x} {y} (q : Q x y)
      → return′-β-left′ q q ∘ return′-glue′ q
      ≡ return′-β-right′ q q
    return′-triangle′ q = Return′.connected-extend-triangle q tt tt

  return : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))
    → τ (n +2+ m) (hfiber glue r₀₁)
  return q₀₀ q₁₁ r₀₁ = τ-extend-nondep ⦃ τ-is-truncated _ _ ⦄ (return′ q₀₀ q₁₁ r₀₁)

  abstract
    return′-β-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r₀ shift
      → return′ q₀ q₁ r₀ (q₁ , shift) ≡ return′-left q₁ q₀ r₀ shift
    return′-β-left q₀ q₁ r₀ shift =
      happly (happly (return′-β-left′ q₀ q₁) r₀) shift

    return′-β-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r₁ shift
      → return′ q₀ q₁ r₁ (q₀ , shift) ≡ return′-right q₀ q₁ r₁ shift
    return′-β-right q₀ q₁ r₁ shift =
      happly (happly (return′-β-right′ q₀ q₁) r₁) shift

    return′-triangle : ∀ {x} {y} (q : Q x y) r shift
      → return′-β-left q q r shift
      ∘ return′-glue q r shift
      ≡ return′-β-right q q r shift
    return′-triangle {x} {y} q r shift =
      let
        fun₁ = return′-β-left′ q q
        fun₂ = return′-β-right′ q q
        glue′ = return′-glue q
      in
        happly (happly fun₁ r) shift ∘ glue′ r shift
          ≡⟨ ap (λ p → happly (happly fun₁ r) shift ∘ p shift)
                $ ! $ happly-funext (glue′ r) ⟩
        happly (happly fun₁ r) shift ∘ happly (funext (glue′ r)) shift
          ≡⟨ concat-ap (λ f → f shift) (happly fun₁ r) $ funext (glue′ r) ⟩
        happly (happly fun₁ r ∘ funext (glue′ r)) shift
          ≡⟨ ap (λ p → happly (happly fun₁ r ∘ p r) shift)
                $ ! $ happly-funext (λ r → funext (glue′ r)) ⟩
        happly (happly fun₁ r ∘ happly (funext λ r → funext (glue′ r)) r) shift
          ≡⟨ ap (λ p → happly p shift) $ concat-ap (λ f → f r) fun₁
              $ funext (λ r → funext (glue′ r)) ⟩
        happly (happly (fun₁ ∘ (funext λ r → funext (glue′ r))) r) shift
          ≡⟨ ap (λ p → happly (happly p r) shift) $ return′-triangle′ q ⟩∎
        happly (happly fun₂ r) shift
          ∎

  -- Equivalence

  {-
      First step:  Pack relevant rules into records.
  -}

  private
    record BetaPair {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀)
      (q₁₁ : Q x₁ y₁) (q₀₁ : Q x₀ y₁) (q₁₀ : Q x₁ y₀)
      (r₀₁ : left x₀ ≡ right y₁) : Set i where
      constructor betaPair
      field
        path : glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁
        cross′-β : ∀ shift → cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)
                           ≡ cross-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ path
        return′-β : ∀ shift → return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)
                            ≡ return-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ path

    β-pair-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r
      → BetaPair q₀ q₁ q₀ q₁ r
    β-pair-left q₀ q₁ r = record
      { path = refl
      ; cross′-β = cross′-β-left q₀ q₁ r
      ; return′-β = return′-β-left q₀ q₁ r
      }

    β-pair-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r
      → BetaPair q₀ q₁ q₁ q₀ r
    β-pair-right q₀ q₁ r = record
      { path = glue-!glue-path q₀ q₁
      ; cross′-β = cross′-β-right q₀ q₁ r
      ; return′-β = return′-β-right q₀ q₁ r
      }

    betaPair≡-raw : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁)
      (q₀₁ : Q x₀ y₁) (q₁₀ : Q x₁ y₀) (r₀₁ : left x₀ ≡ right y₁)
      {p₁ p₂ : glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁} (p≡ : p₁ ≡ p₂)
      {c′β₁} {c′β₂}
      (c′β≡ : transport (λ p → ∀ shift → cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)
                                       ≡ cross-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ p)
                p≡ c′β₁
            ≡ c′β₂)
      {r′β₁} {r′β₂}
      (r′β≡ : transport (λ p → ∀ shift → return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)
                                       ≡ return-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ p)
                p≡ r′β₁
            ≡ r′β₂)
      → betaPair p₁ c′β₁ r′β₁ ≡ betaPair p₂ c′β₂ r′β₂
    betaPair≡-raw _ _ _ _ r refl refl refl = refl

    betaPair≡ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁)
      (q₀₁ : Q x₀ y₁) (q₁₀ : Q x₁ y₀) (r₀₁ : left x₀ ≡ right y₁)
      {p₁ p₂ : glue-!glue q₀₀ q₁₀ ≡ glue-!glue q₀₁ q₁₁} (p≡ : p₁ ≡ p₂)
      {c′β₁} {c′β₂}
      (c′β≡ : ∀ shift → transport (λ p → cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)
                                       ≡ cross-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ p)
                          p≡ (c′β₁ shift)
                      ≡ c′β₂ shift)
      {r′β₁} {r′β₂}
      (r′β≡ : ∀ shift → transport (λ p → return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)
                                       ≡ return-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ p)
                          p≡ (r′β₁ shift)
                      ≡ r′β₂ shift)
      → betaPair p₁ c′β₁ r′β₁ ≡ betaPair p₂ c′β₂ r′β₂
    betaPair≡ q₀₀ q₁₁ q₀₁ q₁₀ r₀₁ refl ct′β≡ cf′β₁≡ =
      betaPair≡-raw q₀₀ q₁₁ q₀₁ q₁₀ r₀₁ refl (funext ct′β≡) (funext cf′β₁≡)

  abstract
    β-pair-glue : ∀ {x} {y} (q : Q x y) r
      → β-pair-left q q r ≡ β-pair-right q q r
    β-pair-glue q r = betaPair≡ q q q q r
        (glue-!glue-path-glue q)
        (λ shift →
          transport
            (λ p → cross′ q q r (q , shift) ≡ cross-template q r shift q q q p)
            (glue-!glue-path-glue q)
            (cross′-β-left q q r shift)
              ≡⟨ trans-cst≡app
                  (cross′ q q r (q , shift))
                  (cross-template q r shift q q q)
                  (glue-!glue-path-glue q)
                  (cross′-β-left q q r shift) ⟩
          cross′-β-left q q r shift ∘ cross′-glue q r shift
              ≡⟨ cross′-triangle q r shift ⟩
          cross′-β-right q q r shift
              ∎)
        (λ shift →
          transport
            (λ p → return′ q q r (q , shift) ≡ return-template q q q r shift q p)
            (glue-!glue-path-glue q)
            (return′-β-left q q r shift)
              ≡⟨ trans-cst≡app
                  (return′ q q r (q , shift))
                  (return-template q q q r shift q)
                  (glue-!glue-path-glue q)
                  (return′-β-left q q r shift) ⟩
          return′-β-left q q r shift ∘ return′-glue q r shift
              ≡⟨ return′-triangle q r shift ⟩
          return′-β-right q q r shift
              ∎)

  -- Lemmas

  return-cross-path-template : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁)
    (q₀₁ : Q x₀ y₁) (q₁₀ : Q x₁ y₀) r shift path
    → return-path-template q₁₀ q₀₀ q₁₁ r (cross-path-template q₀₁ r shift q₀₀ q₁₁ q₁₀ path) q₀₁ path ≡ shift
  return-cross-path-template q₀₀ q₁₁ q₀₁ q₁₀ r shift path =
    anti-whisker-right (! (glue q₁₁)) (! path ∘ path ∘ whisker-right (! (glue q₁₁)) shift)
      ≡⟨ ap (anti-whisker-right (! (glue q₁₁)))
            $ ! $ concat-assoc (! path) path (whisker-right (! (glue q₁₁)) shift) ⟩
    anti-whisker-right (! (glue q₁₁)) ((! path ∘ path) ∘ whisker-right (! (glue q₁₁)) shift)
      ≡⟨ ap (λ p → anti-whisker-right (! (glue q₁₁)) (p ∘ whisker-right (! (glue q₁₁)) shift))
            $ opposite-left-inverse path ⟩
    anti-whisker-right (! (glue q₁₁)) (whisker-right (! (glue q₁₁)) shift)
      ≡⟨ anti-whisker-whisker-right (! (glue q₁₁)) shift ⟩
    shift
      ∎

  cross-return-path-template : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁)
    (q₀₁ : Q x₀ y₁) (q₁₀ : Q x₁ y₀) r shift path
    → cross-path-template q₀₁ r (return-path-template q₁₀ q₀₀ q₁₁ r shift q₀₁ path) q₀₀ q₁₁ q₁₀ path ≡ shift
  cross-return-path-template q₀₀ q₁₁ q₀₁ q₁₀ r shift path =
    path ∘ whisker-right (! (glue q₁₁)) (anti-whisker-right (! (glue q₁₁)) {glue q₀₁} {r} (! path ∘ shift))
      ≡⟨ ap (λ p → path ∘ p) $ whisker-anti-whisker-right (! (glue q₁₁)) {glue q₀₁} {r} (! path ∘ shift) ⟩
    path ∘ ! path ∘ shift
      ≡⟨ ! $ concat-assoc path (! path) shift ⟩
    (path ∘ ! path) ∘ shift
      ≡⟨ ap (λ p → p ∘ shift) $ opposite-right-inverse path ⟩
    shift
      ∎

  -- Templates for both directions

  private
    abstract
      return-cross′-template : ∀ {x₀ x₁} {y₀ y₁} {q₀₀ : Q x₀ y₀}
        {q₁₁ : Q x₁ y₁} {q₀₁ : Q x₀ y₁} {q₁₀ : Q x₁ y₀} {r₀₁}
        (params : BetaPair q₀₀ q₁₁ q₀₁ q₁₀ r₀₁) shift
        → return q₀₀ q₁₁ r₀₁ (cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)) ≡ proj (q₀₁ , shift)
      return-cross′-template {q₀₀ = q₀₀} {q₁₁} {q₀₁} {q₁₀} {r₀₁} params shift =
        return q₀₀ q₁₁ r₀₁ (cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift))
          ≡⟨ ap (return q₀₀ q₁₁ r₀₁) $ cross′-β shift ⟩
        return′ q₀₀ q₁₁ r₀₁ (q₁₀ , cross-path-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ path)
          ≡⟨ return′-β $ cross-path-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ path ⟩
        proj (q₀₁ , return-path-template q₁₀ q₀₀ q₁₁ r₀₁ (cross-path-template q₀₁ r₀₁ shift q₀₀ q₁₁ q₁₀ path) q₀₁ path )
          ≡⟨ ap (λ p → proj (q₀₁ , p)) $ return-cross-path-template q₀₀ q₁₁ q₀₁ q₁₀ r₀₁ shift path ⟩
        proj (q₀₁ , shift)
          ∎
        where open BetaPair params

      cross-return′-template : ∀ {x₀ x₁} {y₀ y₁} {q₀₀ : Q x₀ y₀}
        {q₁₁ : Q x₁ y₁} {q₀₁ : Q x₀ y₁} {q₁₀ : Q x₁ y₀} {r₀₁}
        (params : BetaPair q₀₀ q₁₁ q₀₁ q₁₀ r₀₁) shift
        → cross q₀₀ q₁₁ r₀₁ (return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)) ≡ proj (q₁₀ , shift)
      cross-return′-template {q₀₀ = q₀₀} {q₁₁} {q₀₁} {q₁₀} {r₀₁} params shift =
        cross q₀₀ q₁₁ r₀₁ (return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift))
          ≡⟨ ap (cross q₀₀ q₁₁ r₀₁) $ return′-β shift ⟩
        cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , return-path-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ path)
          ≡⟨ cross′-β $ return-path-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ path ⟩
        proj (q₁₀ , cross-path-template q₀₁ r₀₁ (return-path-template q₁₀ q₀₀ q₁₁ r₀₁ shift q₀₁ path) q₀₀ q₁₁ q₁₀ path )
          ≡⟨ ap (λ p → proj (q₁₀ , p)) $ cross-return-path-template q₀₀ q₁₁ q₀₁ q₁₀ r₀₁ shift path ⟩
        proj (q₁₀ , shift)
          ∎
        where open BetaPair params

  -- Instantiating templates...
  private
    abstract
      return-cross′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
        → return q₀₀ q₁₁ r₀₁ (cross′ q₀₀ q₁₁ r₀₁ s) ≡ proj s
      return-cross′ {x₀}{x₁}{y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₀₁ , shift) = connected-extend
        (point (Σ X λ x → Q x  y₁) (x₀ , q₀₁))
        (point (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁))
        (λ{(x₁ , q₁₁) (y₀ , q₀₀)
            → return q₀₀ q₁₁ r₀₁ (cross′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)) ≡ proj (q₀₁ , shift)})
        {n} {m}
        ⦃ λ _ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₁) (x₀ , q₀₁) (Q-is-conn-y y₁))
        (point-has-connected-fibers (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁) (Q-is-conn-x x₀))
        (λ{(x₁ , q₁₁) _ → return-cross′-template (β-pair-left q₀₁ q₁₁ r₀₁) shift})
        (λ{_ (y₀ , q₀₀) → return-cross′-template (β-pair-right q₀₀ q₀₁ r₀₁) shift})
        (λ _ _ → ap (λ β-pair → return-cross′-template β-pair shift) $ β-pair-glue q₀₁ r₀₁)
        (_ , q₁₁) (_ , q₀₀)

  abstract
    return-cross : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
      → return q₀₀ q₁₁ r₀₁ (cross q₀₀ q₁₁ r₀₁ s) ≡ s
    return-cross q₀₀ q₁₁ r₀₁ = τ-extend
      ⦃ λ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
      (return-cross′ q₀₀ q₁₁ r₀₁)

  {- another direction -}

  private
    abstract
      cross-return′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
        → cross q₀₀ q₁₁ r₀₁ (return′ q₀₀ q₁₁ r₀₁ s) ≡ proj s
      cross-return′ {x₀}{x₁}{y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₁₀ , shift) = connected-extend
        (point (Σ X λ x → Q x  y₀) (x₁ , q₁₀))
        (point (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀))
        (λ{(x₀ , q₀₀) (y₁ , q₁₁) → ∀ r₀₁ shift
            → cross q₀₀ q₁₁ r₀₁ (return′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)) ≡ proj (q₁₀ , shift)})
        {n} {m}
        ⦃ λ _ _ → Π-is-truncated (n +2+ m)
            λ _ → Π-is-truncated (n +2+ m)
            λ _ → ≡-is-truncated (n +2+ m)
                $ τ-is-truncated (n +2+ m) _ ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₀) (x₁ , q₁₀) (Q-is-conn-y y₀))
        (point-has-connected-fibers (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀) (Q-is-conn-x x₁))
        (λ{(x₀ , q₀₀) _ r₀₁ shift → cross-return′-template (β-pair-left q₀₀ q₁₀ r₀₁) shift})
        (λ{_ (y₁ , q₁₁) r₁₁ shift → cross-return′-template (β-pair-right q₁₀ q₁₁ r₁₁) shift})
        (λ _ _ → funext λ r₀₁ → funext λ shift
            → ap (λ β-pair → cross-return′-template β-pair shift) $ β-pair-glue q₁₀ r₀₁)
        (_ , q₀₀) (_ , q₁₁) r₀₁ shift

  abstract
    cross-return : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
      → cross q₀₀ q₁₁ r₀₁ (return q₀₀ q₁₁ r₀₁ s) ≡ s
    cross-return q₀₀ q₁₁ r₀₁ = τ-extend
      ⦃ λ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
      (cross-return′ q₀₀ q₁₁ r₀₁)

  -- OK, we have everything now.

  cross-is-equiv : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → is-equiv (cross q₀₀ q₁₁ r₀₁)
  cross-is-equiv q₀₀ q₁₁ r₀₁ =
    iso-is-eq
      (cross q₀₀ q₁₁ r₀₁)
      (return q₀₀ q₁₁ r₀₁)
      (cross-return q₀₀ q₁₁ r₀₁)
      (return-cross q₀₀ q₁₁ r₀₁)

  cross-equiv : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (hfiber glue r₀₁)
    ≃ τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))
  cross-equiv q₀₀ q₁₁ r₀₁ = cross q₀₀ q₁₁ r₀₁ , cross-is-equiv q₀₀ q₁₁ r₀₁

  cross-path : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (hfiber glue r₀₁)
    ≡ τ (n +2+ m) (hfiber (glue-!glue q₀₀) (r₀₁ ∘ ! (glue q₁₁)))
  cross-path q₀₀ q₁₁ r₀₁ = eq-to-path $ cross-equiv q₀₀ q₁₁ r₀₁
