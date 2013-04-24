{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.BlakersMassey.CoherenceData
  {i} {X Y : Set i} (Q : X → Y → Set i)
  {m} (Q-x-is-conn : ∀ x → is-connected (S m) (Σ Y (λ y → Q x y)))
  {n} (Q-y-is-conn : ∀ y → is-connected (S n) (Σ X (λ x → Q x y)))
  where

  open import Homotopy.PointConnected
  open import Homotopy.Truncation
  open import Homotopy.Extensions.ProductPushoutToProductToConnected
  open import Homotopy.BlakersMassey.PushoutWrapper Q

  abstract
    annoying-path-left : ∀ {i} {X : Set i} {p₀ p₁ p₂ : X}
      (h₁ : p₀ ≡ p₁) (h₂ : p₂ ≡ p₁) → h₁ ∘ (! h₂ ∘ h₂) ≡ h₁
    annoying-path-left h₁ h₂ =
        ap (λ p → h₁ ∘ p) (opposite-left-inverse h₂)
      ∘ refl-right-unit h₁

    annoying-path-right : ∀ {i} {X : Set i} {p₀ p₁ p₂ : X}
      (h₁ : p₀ ≡ p₁) (h₂ : p₀ ≡ p₂)
      → h₁ ∘ (! h₁ ∘ h₂) ≡ h₂
    annoying-path-right h₁ h₂ =
        ! (concat-assoc h₁ (! h₁) h₂)
      ∘ ap (λ p → p ∘ h₂) (opposite-right-inverse h₁)

    annoying-path-lemma : ∀ {i} {X : Set i} {p₀ p₁ : X} (h : p₀ ≡ p₁)
      → annoying-path-left h h ≡ annoying-path-right h h
    annoying-path-lemma refl = refl

  module _ {x₀} {y₁} (q₀₁ : Q x₀ y₁) r₀₁ (shift : glue q₀₁ ≡ r₀₁) where

    coh-to′-left : ∀ {x₁} (q₁₁ : Q x₁ y₁)
      → τ (n +2+ m) (Σ (Q x₁ y₁) (λ q → glue q₀₁ ∘ (! (glue q) ∘ glue q₁₁) ≡ r₀₁))
    coh-to′-left q₁₁ = proj $ q₁₁ , (annoying-path-left  (glue q₀₁) (glue q₁₁) ∘ shift)

    coh-to′-right : ∀ {y₀} (q₀₀ : Q x₀ y₀)
      → τ (n +2+ m) (Σ (Q x₀ y₀) (λ q → glue q₀₀ ∘ (! (glue q) ∘ glue q₀₁) ≡ r₀₁))
    coh-to′-right q₀₀ = proj $ q₀₀ , (annoying-path-right (glue q₀₀) (glue q₀₁) ∘ shift)

    coh-to′-glue : coh-to′-left {x₀} q₀₁ ≡ coh-to′-right {y₁} q₀₁
    coh-to′-glue = ap proj $ Σ-eq refl $ ap (λ p → p ∘ shift) $ annoying-path-lemma (glue q₀₁)

    module CohTo′ where

      open import Homotopy.Extensions.ProductPushoutToProductToConnected
        (point (Σ X λ x → Q x  y₁) (x₀ , q₀₁))
        (point (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁))
        (λ{(x₁ , q₁₁) (y₀ , q₀₀)
            → τ (n +2+ m) (Σ (Q x₁ y₀) (λ q₁₀ → glue q₀₀ ∘ ! (glue q₁₀) ∘ glue q₁₁ ≡ r₀₁))})
        {n} {m}
        ⦃ λ{(x₁ , q₁₁) (y₀ , q₀₀) → τ-is-truncated (n +2+ m)
            (Σ (Q x₁ y₀) (λ q₁₀ → glue q₀₀ ∘ (! (glue q₁₀) ∘ glue q₁₁) ≡ r₀₁))} ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₁) (x₀ , q₀₁) (Q-y-is-conn y₁))
        (point-has-connected-fibers (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁) (Q-x-is-conn x₀))
        (λ{(x₁ , q₁₁) _ → coh-to′-left q₁₁})
        (λ{_ (y₀ , q₀₀) → coh-to′-right q₀₀})
        (λ _ _ → coh-to′-glue)
        public

  abstract
    coh-to′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
      → Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁)
      → τ (n +2+ m) (Σ (Q x₁ y₀) (λ q₁₀ → glue q₀₀ ∘ ! (glue q₁₀) ∘ glue q₁₁ ≡ r₀₁))
    coh-to′ {x₀}{x₁} {y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₀₁ , shift) =
      CohTo′.connected-extend q₀₁ r₀₁ shift (x₁ , q₁₁) (y₀ , q₀₀)

    coh-to′-β-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y)
      r₀ (shift : glue q₀ ≡ r₀)
      → coh-to′ q₀ q₁ r₀ (q₀ , shift) ≡ coh-to′-left q₀ r₀ shift q₁
    coh-to′-β-left {x₀} {x₁} {y} q₀ q₁ r₀ shift =
      CohTo′.connected-extend-β-left q₀ r₀ shift (x₁ , q₁) tt

    coh-to′-β-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁)
      r₁ (shift : glue q₁ ≡ r₁)
      → coh-to′ q₀ q₁ r₁ (q₁ , shift) ≡ coh-to′-right q₁ r₁ shift q₀
    coh-to′-β-right {x} {y₀} {y₁} q₀ q₁ r₁ shift =
      CohTo′.connected-extend-β-right q₁ r₁ shift tt (y₀ , q₀)

    coh-to′-triangle : ∀ {x} {y} (q : Q x y) r (shift : glue q ≡ r)
      → coh-to′-β-left q q r shift
      ∘ coh-to′-glue q r shift
      ≡ coh-to′-β-right q q r shift
    coh-to′-triangle q r shift =
      CohTo′.connected-extend-triangle q r shift tt tt

  coh-to : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))
    → τ (n +2+ m) (Σ (Q x₁ y₀) (λ q → glue q₀₀ ∘ ! (glue q) ∘ glue q₁₁ ≡ r₀₁))
  coh-to q₀₀ q₁₁ r₀₁ = τ-extend ⦃ λ _ → τ-is-truncated _ _ ⦄
    (coh-to′ q₀₀ q₁₁ r₀₁)

  private
    module _ {x₁} {y₀} (q₁₀ : Q x₁ y₀) where
      coh-from′-left : ∀ {x₀} (q₀₀ : Q x₀ y₀)
        r₀₀ (shift : glue q₀₀ ∘ ! (glue q₁₀) ∘ glue q₁₀ ≡ r₀₀)
        → τ (n +2+ m) (Σ (Q x₀ y₀) (λ q → glue q ≡ r₀₀))
      coh-from′-left q₀₀ _ shift =
        proj $ q₀₀ , (! (annoying-path-left  (glue q₀₀) (glue q₁₀)) ∘ shift)

      coh-from′-right : ∀ {y₁} (q₁₁ : Q x₁ y₁)
        r₁₁ (shift : glue q₁₀ ∘ ! (glue q₁₀) ∘ glue q₁₁ ≡ r₁₁)
        → τ (n +2+ m) (Σ (Q x₁ y₁) (λ q → glue q ≡ r₁₁))
      coh-from′-right q₁₁ _ shift =
        proj $ q₁₁ , (! (annoying-path-right (glue q₁₀) (glue q₁₁)) ∘ shift)

      coh-from′-glue : ∀ r₀₁ shift
        → coh-from′-left q₁₀ r₀₁ shift ≡ coh-from′-right q₁₀ r₀₁ shift
      coh-from′-glue r₀₁ shift =
        ap proj $ Σ-eq refl $ ap (λ p → ! p ∘ shift) $ annoying-path-lemma (glue q₁₀)

      coh-from′-glue′ : coh-from′-left q₁₀ ≡ coh-from′-right q₁₀
      coh-from′-glue′ = funext λ r₀₁ → funext λ shift → coh-from′-glue r₀₁ shift

      module CohFrom′ where
        open import Homotopy.Extensions.ProductPushoutToProductToConnected
          (point (Σ X λ x → Q x  y₀) (x₁ , q₁₀))
          (point (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀))
          (λ{(x₀ , q₀₀) (y₁ , q₁₁) → ∀ r₀₁ (shift : glue q₀₀ ∘ ! (glue q₁₀) ∘ glue q₁₁ ≡ r₀₁)
              → τ (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))})
          {n} {m}
          ⦃ λ{(x₀ , q₀₀) (y₁ , q₁₁) → Π-is-truncated (n +2+ m) λ r₀₁
                  → Π-is-truncated (n +2+ m) λ shift
                  → τ-is-truncated (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))} ⦄
          (point-has-connected-fibers (Σ X λ x → Q x  y₀) (x₁ , q₁₀) (Q-y-is-conn y₀))
          (point-has-connected-fibers (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀) (Q-x-is-conn x₁))
          (λ{(x₀ , q₀₀) _ → coh-from′-left q₀₀})
          (λ{_ (y₁ , q₁₁) → coh-from′-right q₁₁})
          (λ _ _ → coh-from′-glue′)
          public

  abstract
    coh-from′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
      → Σ (Q x₁ y₀) (λ q₁₀ → glue q₀₀ ∘ ! (glue q₁₀) ∘ glue q₁₁ ≡ r₀₁)
      → τ (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))
    coh-from′ {x₀}{x₁} {y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₁₀ , shift) =
      CohFrom′.connected-extend q₁₀ (x₀ , q₀₀) (y₁ , q₁₁) r₀₁ shift

    coh-from′-β-left′ : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y)
      → (λ r₀ shift → coh-from′ q₀ q₁ r₀ (q₁ , shift))
      ≡ coh-from′-left q₁ q₀
    coh-from′-β-left′ {x₀} q₀ q₁ =
      CohFrom′.connected-extend-β-left q₁ (x₀ , q₀) tt

    coh-from′-β-right′ : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁)
      → (λ r₁ shift → coh-from′ q₀ q₁ r₁ (q₀ , shift))
      ≡ coh-from′-right q₀ q₁
    coh-from′-β-right′ {y₁ = y₁} q₀ q₁ =
      CohFrom′.connected-extend-β-right q₀ tt (y₁ , q₁)

    coh-from′-triangle′ : ∀ {x} {y} (q : Q x y)
      → coh-from′-β-left′ q q ∘ coh-from′-glue′ q
      ≡ coh-from′-β-right′ q q
    coh-from′-triangle′ q = CohFrom′.connected-extend-triangle q tt tt

  coh-from : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (Σ (Q x₁ y₀) (λ q → glue q₀₀ ∘ ! (glue q) ∘ glue q₁₁ ≡ r₀₁))
    → τ (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))
  coh-from q₀₀ q₁₁ r₀₁ = τ-extend ⦃ λ _ → τ-is-truncated _ _ ⦄
    (coh-from′ q₀₀ q₁₁ r₀₁)

  abstract
    coh-from′-β-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r₀ shift
      → coh-from′ q₀ q₁ r₀ (q₁ , shift) ≡ coh-from′-left q₁ q₀ r₀ shift
    coh-from′-β-left q₀ q₁ r₀ shift =
      happly (happly (coh-from′-β-left′ q₀ q₁) r₀) shift

    coh-from′-β-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r₁ shift
      → coh-from′ q₀ q₁ r₁ (q₀ , shift) ≡ coh-from′-right q₀ q₁ r₁ shift
    coh-from′-β-right q₀ q₁ r₁ shift =
      happly (happly (coh-from′-β-right′ q₀ q₁) r₁) shift

    coh-from′-triangle : ∀ {x} {y} (q : Q x y)
      (r : left x ≡ right y) (shift : glue q ∘ ! (glue q) ∘ glue q ≡ r)
      → coh-from′-β-left q q r shift
      ∘ coh-from′-glue q r shift
      ≡ coh-from′-β-right q q r shift
    coh-from′-triangle {x} {y} q r shift =
      let
        fun₁ = coh-from′-β-left′ q q
        fun₂ = coh-from′-β-right′ q q
        glue′ = coh-from′-glue q
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
          ≡⟨ ap (λ p → happly (happly p r) shift) $ coh-from′-triangle′ q ⟩∎
        happly (happly fun₂ r) shift
          ∎

  {-
    The following code proves that the coherence data for from's and to's
    agree when both x's and y's collapse.  Relevant data are packed into
    a record [BetaPair] and a path is provided.
  -}

  private
    trans-cst≡projΣ : ∀ {i j} {A : Set i} {B : A → Set j}
      (s : τ (n +2+ m) (Σ A B)) {a : A} {b₁ b₂ : B a}
      (p : b₁ ≡ b₂) (path : s ≡ proj (a , b₁))
      → transport (λ x → s ≡ proj (a , x)) p path
      ≡ path ∘ (ap proj $ Σ-eq refl p)
    trans-cst≡projΣ s refl path = ! $ refl-right-unit _

  private
    record BetaPair {x} {y} (q : Q x y) r : Set i where
      constructor betaPair
      field
        annoying-path : glue q ∘ ! (glue q) ∘ glue q ≡ glue q
        coh-to′-β : ∀ shift →
            coh-to′ q q r (q , shift)
          ≡ proj (q , (annoying-path ∘ shift))
        coh-from′-β : ∀ shift →
            coh-from′ q q r (q , shift)
          ≡ proj (q , (! annoying-path ∘ shift))

    coh-β-left : ∀ {x} {y} (q : Q x y) r
      → BetaPair q r
    coh-β-left q r =
      let annoying-path = annoying-path-left (glue q) (glue q)
      in record
          { annoying-path = annoying-path
          ; coh-to′-β = coh-to′-β-left q q r
          ; coh-from′-β = coh-from′-β-left q q r
          }

    coh-β-right : ∀ {x} {y} (q : Q x y) r
      → BetaPair q r
    coh-β-right q r =
      let annoying-path = annoying-path-right (glue q) (glue q)
      in record
          { annoying-path = annoying-path
          ; coh-to′-β = coh-to′-β-right q q r
          ; coh-from′-β = coh-from′-β-right q q r
          }

    betaPair=-raw : ∀ {x} {y} (q : Q x y) (r : left x ≡ right y)
      {ap₁ ap₂ : glue q ∘ ! (glue q) ∘ glue q ≡ glue q} (ap≡ : ap₁ ≡ ap₂)
      {ct′β₁ : ∀ shift → coh-to′ q q r (q , shift) ≡ proj (q , (ap₁ ∘ shift))}
      {ct′β₂ : ∀ shift → coh-to′ q q r (q , shift) ≡ proj (q , (ap₂ ∘ shift))}
      (ct′β≡ : transport (λ ap → ∀ shift → coh-to′ q q r (q , shift) ≡ proj (q , (ap ∘ shift))) ap≡ ct′β₁
             ≡ ct′β₂)
      {cf′β₁ : ∀ shift → coh-from′ q q r (q , shift) ≡ proj (q , (! ap₁ ∘ shift))}
      {cf′β₂ : ∀ shift → coh-from′ q q r (q , shift) ≡ proj (q , (! ap₂ ∘ shift))}
      (ct′β≡ : transport (λ ap → ∀ shift → coh-from′ q q r (q , shift) ≡ proj (q , (! ap ∘ shift))) ap≡ cf′β₁
             ≡ cf′β₂)
      → betaPair ap₁ ct′β₁ cf′β₁ ≡ betaPair ap₂ ct′β₂ cf′β₂
    betaPair=-raw q r refl refl refl = refl

    betaPair= : ∀ {x} {y} (q : Q x y) (r : left x ≡ right y)
      {ap₁ ap₂ : glue q ∘ ! (glue q) ∘ glue q ≡ glue q} (ap≡ : ap₁ ≡ ap₂)
      {ct′β₁ : ∀ shift → coh-to′ q q r (q , shift) ≡ proj (q , (ap₁ ∘ shift))}
      {ct′β₂ : ∀ shift → coh-to′ q q r (q , shift) ≡ proj (q , (ap₂ ∘ shift))}
      (ct′β≡ : ∀ shift → transport (λ ap → coh-to′ q q r (q , shift) ≡ proj (q , (ap ∘ shift))) ap≡ (ct′β₁ shift)
                       ≡ ct′β₂ shift)
      {cf′β₁ : ∀ shift → coh-from′ q q r (q , shift) ≡ proj (q , (! ap₁ ∘ shift))}
      {cf′β₂ : ∀ shift → coh-from′ q q r (q , shift) ≡ proj (q , (! ap₂ ∘ shift))}
      (ct′β≡ : ∀ shift → transport (λ ap → coh-from′ q q r (q , shift) ≡ proj (q , (! ap ∘ shift))) ap≡ (cf′β₁ shift)
                       ≡ cf′β₂ shift)
      → betaPair ap₁ ct′β₁ cf′β₁ ≡ betaPair ap₂ ct′β₂ cf′β₂
    betaPair= q r refl ct′β≡ cf′β₁≡ = betaPair=-raw q r refl (funext ct′β≡) (funext cf′β₁≡)

  abstract
    coh-β-glue : ∀ {x} {y} (q : Q x y) r
      → coh-β-left q r
      ≡ coh-β-right q r
    coh-β-glue q r = betaPair= q r
        (annoying-path-lemma (glue q))
        (λ shift →
          transport
            (λ ap → coh-to′ q q r (q , shift) ≡ proj (q , (ap ∘ shift)))
            (annoying-path-lemma (glue q))
            (coh-to′-β-left q q r shift)
              ≡⟨ ! $ trans-ap
                      (λ apshift → coh-to′ q q r (q , shift) ≡ proj (q , apshift))
                      (λ p → p ∘ shift)
                      (annoying-path-lemma (glue q))
                      (coh-to′-β-left q q r shift) ⟩
          transport
            (λ apshift → coh-to′ q q r (q , shift) ≡ proj (q , apshift))
            (ap (λ p → p ∘ shift) $ annoying-path-lemma (glue q))
            (coh-to′-β-left q q r shift)
              ≡⟨ trans-cst≡projΣ
                  (coh-to′ q q r (q , shift))
                  (ap (λ p → p ∘ shift) $ annoying-path-lemma (glue q))
                  (coh-to′-β-left q q r shift) ⟩
          coh-to′-β-left q q r shift ∘ coh-to′-glue q r shift
              ≡⟨ coh-to′-triangle q r shift ⟩
          coh-to′-β-right q q r shift
              ∎)
        (λ shift →
          transport
            (λ ap → coh-from′ q q r (q , shift) ≡ proj (q , (! ap ∘ shift)))
            (annoying-path-lemma (glue q))
            (coh-from′-β-left q q r shift)
              ≡⟨ ! $ trans-ap
                      (λ !apshift → coh-from′ q q r (q , shift) ≡ proj (q , !apshift))
                      (λ p → ! p ∘ shift)
                      (annoying-path-lemma (glue q))
                      (coh-from′-β-left q q r shift) ⟩
          transport
            (λ apshift → coh-from′ q q r (q , shift) ≡ proj (q , apshift))
            (ap (λ p → ! p ∘ shift) $ annoying-path-lemma (glue q))
            (coh-from′-β-left q q r shift)
              ≡⟨ trans-cst≡projΣ
                  (coh-from′ q q r (q , shift))
                  (ap (λ p → ! p ∘ shift) $ annoying-path-lemma (glue q))
                  (coh-from′-β-left q q r shift) ⟩
          coh-from′-β-left q q r shift ∘ coh-from′-glue q r shift
              ≡⟨ coh-from′-triangle q r shift ⟩
          coh-from′-β-right q q r shift
              ∎)

  -- Equivalence

  -- from-to

  private
    abstract
      coh-from-to′-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r₀ shift
        → coh-from q₀ q₁ r₀ (coh-to′ q₀ q₁ r₀ (q₀ , shift)) ≡ proj (q₀ , shift)
      coh-from-to′-left q₀ q₁ r₀ shift =
        let
          annoying-path = annoying-path-left (glue q₀) (glue q₁)
        in
          coh-from q₀ q₁ r₀ (coh-to′ q₀ q₁ r₀ (q₀ , shift))
            ≡⟨ ap (coh-from q₀ q₁ r₀) $ coh-to′-β-left q₀ q₁ r₀ shift ⟩
          coh-from′ q₀ q₁ r₀ (q₁ , (annoying-path ∘ shift))
            ≡⟨ coh-from′-β-left q₀ q₁ r₀ (annoying-path ∘ shift) ⟩
          proj (q₀ , (! annoying-path ∘ annoying-path ∘ shift))
            ≡⟨ ap (λ p → proj (q₀ , p)) $ ! $ concat-assoc (! annoying-path) annoying-path shift ⟩
          proj (q₀ , ((! annoying-path ∘ annoying-path) ∘ shift))
            ≡⟨ ap (λ p → proj (q₀ , (p ∘ shift))) $ opposite-left-inverse annoying-path ⟩
          proj (q₀ , shift)
            ∎

      coh-from-to′-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r₁ shift
        → coh-from q₀ q₁ r₁ (coh-to′ q₀ q₁ r₁ (q₁ , shift)) ≡ proj (q₁ , shift)
      coh-from-to′-right q₀ q₁ r₁ shift =
        let
          annoying-path = annoying-path-right (glue q₀) (glue q₁)
        in
          coh-from q₀ q₁ r₁ (coh-to′ q₀ q₁ r₁ (q₁ , shift))
            ≡⟨ ap (coh-from q₀ q₁ r₁) $ coh-to′-β-right q₀ q₁ r₁ shift ⟩
          coh-from′ q₀ q₁ r₁ (q₀ , (annoying-path ∘ shift))
            ≡⟨ coh-from′-β-right q₀ q₁ r₁ (annoying-path ∘ shift) ⟩
          proj (q₁ , (! annoying-path ∘ annoying-path ∘ shift))
            ≡⟨ ap (λ p → proj (q₁ , p)) $ ! $ concat-assoc (! annoying-path) annoying-path shift ⟩
          proj (q₁ , ((! annoying-path ∘ annoying-path) ∘ shift))
            ≡⟨ ap (λ p → proj (q₁ , (p ∘ shift))) $ opposite-left-inverse annoying-path ⟩
          proj (q₁ , shift)
            ∎

      coh-from-to′-glue-template : ∀ {x} {y} (q : Q x y) r
        → BetaPair q r → ∀ shift
        → coh-from q q r (coh-to′ q q r (q , shift)) ≡ proj (q , shift)
      coh-from-to′-glue-template q r params shift = let open BetaPair params in
        coh-from q q r (coh-to′ q q r (q , shift))
          ≡⟨ ap (coh-from q q r) $ coh-to′-β shift ⟩
        coh-from′ q q r (q , (annoying-path ∘ shift))
          ≡⟨ coh-from′-β (annoying-path ∘ shift) ⟩
        proj (q , (! annoying-path ∘ annoying-path ∘ shift))
          ≡⟨ ap (λ p → proj (q , p)) $ ! $ concat-assoc (! annoying-path) annoying-path shift ⟩
        proj (q , ((! annoying-path ∘ annoying-path) ∘ shift))
          ≡⟨ ap (λ p → proj (q , (p ∘ shift))) $ opposite-left-inverse annoying-path ⟩
        proj (q , shift)
          ∎

      coh-from-to′-glue : ∀ {x} {y} (q : Q x y) r shift
        → coh-from-to′-left q q r shift ≡ coh-from-to′-right q q r shift
      coh-from-to′-glue q r shift =
        ap (λ bp → coh-from-to′-glue-template q r bp shift) (coh-β-glue q r)

    abstract
      coh-from-to′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
        → coh-from q₀₀ q₁₁ r₀₁ (coh-to′ q₀₀ q₁₁ r₀₁ s) ≡ proj s
      coh-from-to′ {x₀}{x₁}{y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₀₁ , shift) = connected-extend
        (point (Σ X λ x → Q x  y₁) (x₀ , q₀₁))
        (point (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁))
        (λ{(x₁ , q₁₁) (y₀ , q₀₀)
            → coh-from q₀₀ q₁₁ r₀₁ (coh-to′ q₀₀ q₁₁ r₀₁ (q₀₁ , shift)) ≡ proj (q₀₁ , shift)})
        {n} {m}
        ⦃ λ{(x₁ , q₁₁) (y₀ , q₀₀) → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _} ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₁) (x₀ , q₀₁) (Q-y-is-conn y₁))
        (point-has-connected-fibers (Σ Y λ y → Q x₀ y ) (y₁ , q₀₁) (Q-x-is-conn x₀))
        (λ{(x₁ , q₁₁) _ → coh-from-to′-left q₀₁ q₁₁ r₀₁ shift})
        (λ{_ (y₀ , q₀₀) → coh-from-to′-right q₀₀ q₀₁ r₀₁ shift})
        (λ _ _ → coh-from-to′-glue q₀₁ r₀₁ shift)
        (_ , q₁₁) (_ , q₀₀)

  abstract
    coh-from-to : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
      → coh-from q₀₀ q₁₁ r₀₁ (coh-to q₀₀ q₁₁ r₀₁ s) ≡ s
    coh-from-to q₀₀ q₁₁ r₀₁ = τ-extend
      ⦃ λ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
      (coh-from-to′ q₀₀ q₁₁ r₀₁)

  -- to-from

  private
    abstract
      coh-to-from′-left : ∀ {x₀ x₁} {y} (q₀ : Q x₀ y) (q₁ : Q x₁ y) r₀ shift
        → coh-to q₀ q₁ r₀ (coh-from′ q₀ q₁ r₀ (q₁ , shift)) ≡ proj (q₁ , shift)
      coh-to-from′-left q₀ q₁ r₀ shift =
        let
          annoying-path = annoying-path-left (glue q₀) (glue q₁)
        in
          coh-to q₀ q₁ r₀ (coh-from′ q₀ q₁ r₀ (q₁ , shift))
            ≡⟨ ap (coh-to q₀ q₁ r₀) $ coh-from′-β-left q₀ q₁ r₀ shift ⟩
          coh-to′ q₀ q₁ r₀ (q₀ , (! annoying-path ∘ shift))
            ≡⟨ coh-to′-β-left q₀ q₁ r₀ (! annoying-path ∘ shift) ⟩
          proj (q₁ , (annoying-path ∘ ! annoying-path ∘ shift))
            ≡⟨ ap (λ p → proj (q₁ , p)) $ ! $ concat-assoc annoying-path (! annoying-path) shift ⟩
          proj (q₁ , ((annoying-path ∘ ! annoying-path) ∘ shift))
            ≡⟨ ap (λ p → proj (q₁ , (p ∘ shift))) $ opposite-right-inverse annoying-path ⟩∎
          proj (q₁ , shift)
            ∎

      coh-to-from′-right : ∀ {x} {y₀ y₁} (q₀ : Q x y₀) (q₁ : Q x y₁) r₁ shift
        → coh-to q₀ q₁ r₁ (coh-from′ q₀ q₁ r₁ (q₀ , shift)) ≡ proj (q₀ , shift)
      coh-to-from′-right q₀ q₁ r₁ shift =
        let
          annoying-path = annoying-path-right (glue q₀) (glue q₁)
        in
          coh-to q₀ q₁ r₁ (coh-from′ q₀ q₁ r₁ (q₀ , shift))
            ≡⟨ ap (coh-to q₀ q₁ r₁) $ coh-from′-β-right q₀ q₁ r₁ shift ⟩
          coh-to′ q₀ q₁ r₁ (q₁ , (! annoying-path ∘ shift))
            ≡⟨ coh-to′-β-right q₀ q₁ r₁ (! annoying-path ∘ shift) ⟩
          proj (q₀ , (annoying-path ∘ ! annoying-path ∘ shift))
            ≡⟨ ap (λ p → proj (q₀ , p)) $ ! $ concat-assoc annoying-path (! annoying-path) shift ⟩
          proj (q₀ , ((annoying-path ∘ ! annoying-path) ∘ shift))
            ≡⟨ ap (λ p → proj (q₀ , (p ∘ shift))) $ opposite-right-inverse annoying-path ⟩
          proj (q₀ , shift)
            ∎

      coh-to-from′-glue-template : ∀ {x} {y} (q : Q x y) r
        → BetaPair q r → ∀ shift
        → coh-to q q r (coh-from′ q q r (q , shift)) ≡ proj (q , shift)
      coh-to-from′-glue-template q r params shift = let open BetaPair params in
        coh-to q q r (coh-from′ q q r (q , shift))
          ≡⟨ ap (coh-to q q r) $ coh-from′-β shift ⟩
        coh-to′ q q r (q , (! annoying-path ∘ shift))
          ≡⟨ coh-to′-β (! annoying-path ∘ shift) ⟩
        proj (q , (annoying-path ∘ ! annoying-path ∘ shift))
          ≡⟨ ap (λ p → proj (q , p)) $ ! $ concat-assoc annoying-path (! annoying-path) shift ⟩
        proj (q , ((annoying-path ∘ ! annoying-path) ∘ shift))
          ≡⟨ ap (λ p → proj (q , (p ∘ shift))) $ opposite-right-inverse annoying-path ⟩
        proj (q , shift)
          ∎

      coh-to-from′-glue : ∀ {x} {y} (q : Q x y) r shift
        → coh-to-from′-left q q r shift ≡ coh-to-from′-right q q r shift
      coh-to-from′-glue q r shift =
        ap (λ bp → coh-to-from′-glue-template q r bp shift) (coh-β-glue q r)

    abstract
      coh-to-from′ : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
        → coh-to q₀₀ q₁₁ r₀₁ (coh-from′ q₀₀ q₁₁ r₀₁ s) ≡ proj s
      coh-to-from′ {x₀}{x₁}{y₀}{y₁} q₀₀ q₁₁ r₀₁ (q₁₀ , shift) = connected-extend
        (point (Σ X λ x → Q x  y₀) (x₁ , q₁₀))
        (point (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀))
        (λ{(x₀ , q₀₀) (y₁ , q₁₁) → ∀ r₀₁ shift
            → coh-to q₀₀ q₁₁ r₀₁ (coh-from′ q₀₀ q₁₁ r₀₁ (q₁₀ , shift)) ≡ proj (q₁₀ , shift)})
        {n} {m}
        ⦃ λ{(x₀ , q₀₀) (y₁ , q₁₁) → Π-is-truncated (n +2+ m) λ r₀₁
            → Π-is-truncated (n +2+ m) λ shift
            → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _} ⦄
        (point-has-connected-fibers (Σ X λ x → Q x  y₀) (x₁ , q₁₀) (Q-y-is-conn y₀))
        (point-has-connected-fibers (Σ Y λ y → Q x₁ y ) (y₀ , q₁₀) (Q-x-is-conn x₁))
        (λ{(x₀ , q₀₀) _ → coh-to-from′-left q₀₀ q₁₀})
        (λ{_ (y₁ , q₁₁) → coh-to-from′-right q₁₀ q₁₁})
        (λ _ _ → funext λ r₀₁ → funext λ shift → coh-to-from′-glue q₁₀ r₀₁ shift)
        (_ , q₀₀) (_ , q₁₁) r₀₁ shift

  abstract
    coh-to-from : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁ s
      → coh-to q₀₀ q₁₁ r₀₁ (coh-from q₀₀ q₁₁ r₀₁ s) ≡ s
    coh-to-from q₀₀ q₁₁ r₀₁ = τ-extend
      ⦃ λ _ → ≡-is-truncated (n +2+ m) $ τ-is-truncated (n +2+ m) _ ⦄
      (coh-to-from′ q₀₀ q₁₁ r₀₁)

  coh-to-is-equiv : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → is-equiv (coh-to q₀₀ q₁₁ r₀₁)
  coh-to-is-equiv q₀₀ q₁₁ r₀₁ =
    iso-is-eq
      (coh-to q₀₀ q₁₁ r₀₁)
      (coh-from q₀₀ q₁₁ r₀₁)
      (coh-to-from q₀₀ q₁₁ r₀₁)
      (coh-from-to q₀₀ q₁₁ r₀₁)

  coh-to-equiv : ∀ {x₀ x₁} {y₀ y₁} (q₀₀ : Q x₀ y₀) (q₁₁ : Q x₁ y₁) r₀₁
    → τ (n +2+ m) (Σ (Q x₀ y₁) (λ q₀₁ → glue q₀₁ ≡ r₀₁))
    ≃ τ (n +2+ m) (Σ (Q x₁ y₀) (λ q → glue q₀₀ ∘ ! (glue q) ∘ glue q₁₁ ≡ r₀₁))
  coh-to-equiv q₀₀ q₁₁ r₀₁ = coh-to q₀₀ q₁₁ r₀₁ , coh-to-is-equiv q₀₀ q₁₁ r₀₁
