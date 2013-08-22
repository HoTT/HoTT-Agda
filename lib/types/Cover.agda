{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.TLevel
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.LoopSpace

module lib.types.Cover {i} where

{-
  The definition of covering spaces.
-}
record Cover (A : Type i) {j} : Type (lmax i (lsucc j)) where
  constructor cover
  field
    Fiber : A → Type j
    Fiber-level : ∀ a → is-set (Fiber a)
  Fiber-is-set = Fiber-level

-- Basic tools
module _ {A : Type i} {j} where

  open Cover

  private
    cover=′ : (c₁ c₂ : Cover A {j}) → Fiber c₁ == Fiber c₂ → c₁ == c₂
    cover=′ (cover f _) (cover .f _) idp = ap (cover f) $
      prop-has-all-paths (Π-is-prop λ _ → is-set-is-prop) _ _

  cover= : (c₁ c₂ : Cover A {j}) → (∀ a → Fiber c₁ a ≃ Fiber c₂ a)
    → c₁ == c₂
  cover= c₁ c₂ F≃ = cover=′ c₁ c₂ (λ= λ a → ua $ F≃ a)

  -- The definition of universality in terms of connectedness.
  is-universal : Cover A {j} → Type (lmax i j)
  is-universal (cover F _) = is-connected ⟨1⟩ $ Σ A F

  -- In terms of connectedness
  UniversalCover : Type (lmax i (lsucc j))
  UniversalCover = Σ (Cover A {j}) is-universal

-- Theorem: A covering space keeps higher homotopy groups.
module _ (A∙ : Ptd i)
  {j} (c : Cover (fst A∙) {j})
  (a↑ : Cover.Fiber c (snd A∙)) where

  open Cover c
  private
    F = Cover.Fiber c
    F-level = Cover.Fiber-level c
    A = fst A∙
    a = snd A∙

  private
    -- The projection map with one end free (in order to apply J).
    to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
        → idp == p⇑ → idp == fst= p⇑
    to′ idp=p⇑ = ap fst= idp=p⇑

    -- The projection map from Ω²(Σ A F) to Ω²(A).
    to : Ω^ 2 ∙[ Σ A F , (a , a↑) ] → Ω^ 2 A∙
    to p²⇑ = to′ {p⇑ = idp} p²⇑

    -- Auxiliary synthesized path for injection.
    idp=p↑ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
             → (idp=p : idp == p)
             → idp == p↑
               [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
    idp=p↑ idp = prop-has-all-paths (F-level a _ _) _ _

    -- The injection map with some ends free (in order to apply J).
    from′ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
            → (idp=p : idp == p)
            → idp == p↑ -- aux
              [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
            → idp == pair= p p↑
    from′ idp=p idp=p↑ = pair== idp=p idp=p↑

    -- The injection map from Ω²(A) to Ω²(Σ A F).
    from : Ω^ 2 A∙ → Ω^ 2 ∙[ Σ A F , (a , a↑) ]
    from p² = from′ {p = idp} {p↑ = idp} p² (idp=p↑ p²)

    -- Injection is left-inverse to projection (with some ends free).
    from′-to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
                → (idp=p⇑ : idp == p⇑)
                → (idp=snd=p⇑ : idp == snd= p⇑ -- aux
                  [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ to′ idp=p⇑ ])
                → from′ (to′ idp=p⇑) idp=snd=p⇑ == idp=p⇑
                  [ (λ p⇑ → idp == p⇑) ↓ ! (pair=-η p⇑) ]
    from′-to′ idp idp = idp

    -- Injection is left-inverse to projection.
    from-to : ∀ p²⇑ → from (to p²⇑) == p²⇑
    from-to p²⇑ = from′-to′ {p⇑ = idp} p²⇑ (idp=p↑ (to′ p²⇑))

    -- Injection is right-inverse to projection (with some ends free).
    to′-from′ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
                → (idp=p : idp == p)
                → (idp=p↑ : idp == p↑ -- aux
                  [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ])
                → to′ (from′ idp=p idp=p↑) == idp=p
                  [ (λ p → idp == p) ↓ fst=-β p p↑ ]
    to′-from′ idp idp = idp

    -- Injection is right-inverse to projection.
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
