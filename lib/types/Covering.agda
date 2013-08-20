{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.TLevel
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.LoopSpace

module lib.types.Covering {i} where

{-
  The definition of covering spaces.
-}
record Covering (A : Type i) {j} : Type (lmax i (lsucc j)) where
  constructor covering
  field
    Fiber : A → Type j
    Fiber-level : ∀ a → is-set (Fiber a)

-- Basic tools
module _ {A : Type i} {j} where

  open Covering

  private
    covering=′ : (c₁ c₂ : Covering A {j}) → Fiber c₁ == Fiber c₂ → c₁ == c₂
    covering=′ (covering f _) (covering .f _) idp = ap (covering f) $
      prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _

  covering= : (c₁ c₂ : Covering A {j}) → (∀ a → Fiber c₁ a ≃ Fiber c₂ a)
    → c₁ == c₂
  covering= c₁ c₂ F≃ = covering=′ c₁ c₂ (λ= λ a → ua $ F≃ a)

  -- The definition of universality in terms of connectedness.
  is-universal : Covering A {j} → Type (lmax i j)
  is-universal (covering F _) = is-connected ⟨1⟩ $ Σ A F

  -- In terms of connectedness
  UniversalCovering : Type (lmax i (lsucc j))
  UniversalCovering = Σ (Covering A {j}) is-universal

-- Theorem: A covering space keeps higher homotopy groups.
module _ (A∙ : Ptd i)
  {j} (c : Covering (fst A∙) {j})
  (a↑ : Covering.Fiber c (snd A∙)) where

  open Covering c
  private
    F = Covering.Fiber c
    F-level = Covering.Fiber-level c
    A = fst A∙
    a = snd A∙

  private
    to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
        → idp == p⇑ → idp == fst= p⇑
    to′ idp=p⇑ = ap fst= idp=p⇑

    -- The projection map from Ω²(Σ A F) to Ω²(A).
    to : Ω^ 2 ∙[ Σ A F , (a , a↑) ] → Ω^ 2 A∙
    to p²⇑ = to′ {p⇑ = idp} p²⇑

    -- aux
    idp=p↑ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
             → (idp=p : idp == p)
             → idp == p↑
               [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
    idp=p↑ idp = prop-has-all-paths (F-level a _ _) _ _

    from′ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
            → (idp=p : idp == p)
            → idp == p↑ -- aux
              [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
            → idp == pair= p p↑
    from′ idp=p idp=p↑ = pair== idp=p idp=p↑

    -- The injection map from Ω²(A) to Ω²(Σ A F).
    from : Ω^ 2 A∙ → Ω^ 2 ∙[ Σ A F , (a , a↑) ]
    from p² = from′ {p = idp} {p↑ = idp} p² (idp=p↑ p²)

    from′-to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
                → (idp=p⇑ : idp == p⇑)
                → (idp=snd=p⇑ : idp == snd= p⇑ -- aux
                  [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ to′ idp=p⇑ ])
                → from′ (to′ idp=p⇑) idp=snd=p⇑ == idp=p⇑
                  [ (λ p⇑ → idp == p⇑) ↓ ! (pair=-η p⇑) ]
    from′-to′ idp idp = idp

    from-to : ∀ p²⇑ → from (to p²⇑) == p²⇑
    from-to p²⇑ = from′-to′ {p⇑ = idp} p²⇑ (idp=p↑ (to′ p²⇑))

    to′-from′ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
                → (idp=p : idp == p)
                → (idp=p↑ : idp == p↑ -- aux
                  [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ])
                → to′ (from′ idp=p idp=p↑) == idp=p
                  [ (λ p → idp == p) ↓ fst=-β p p↑ ]
    to′-from′ idp idp = idp

    to-from : ∀ p² → to (from p²) == p²
    to-from p² = to′-from′ p² (idp=p↑ p²)

  -- The theorem.
  Ω²ΣAFiber≃Ω²A : Ω^ 2 (Σ A F , (a , a↑)) ≃ Ω^ 2 A∙
  Ω²ΣAFiber≃Ω²A = to , is-eq to from to-from from-to

{-
tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂} → fiber a₁ → a₁ ≡₀ a₂ → fiber a₂
tracing cov[ fiber , fiber-is-set ] y =
  π₀-extend-nondep
    ⦃ fiber-is-set _ ⦄
    (λ p → transport fiber p y)

compose-tracing : ∀ cov → let open covering cov in
  ∀ {a₁ a₂ a₃} y (p₁ : a₁ ≡₀ a₂) (p₂ : a₂ ≡₀ a₃)
  → tracing cov (tracing cov y p₁) p₂ ≡ tracing cov y (p₁ ∘₀ p₂)
compose-tracing cov y = let open covering cov in
  π₀-extend
    ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ fiber-is-set _ ⦄
    (λ p₁ → π₀-extend
      ⦃ λ _ → ≡-is-set $ fiber-is-set _ ⦄
      (λ p₂ → compose-trans fiber p₂ p₁ y))
-}
