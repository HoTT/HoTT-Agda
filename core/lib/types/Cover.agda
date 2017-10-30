{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics renaming (pt to pt⊙)
open import lib.NConnected
open import lib.types.TLevel
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.types.PathSet

module lib.types.Cover {i} where

{-
  The definition of covering spaces.
-}
record Cover (A : Type i) j : Type (lmax i (lsucc j)) where
  constructor cover
  field
    Fiber : A → Type j
    {{Fiber-level}} : ∀ {a} → is-set (Fiber a)

  Fiber-is-set = Fiber-level
  TotalSpace = Σ A Fiber

⊙Cover : ∀ (X : Ptd i) j → Type (lmax i (lsucc j))
⊙Cover X j = Σ (Cover (de⊙ X) j) λ C → Cover.Fiber C (pt⊙ X)

module ⊙Cover {X : Ptd i} {j} (⊙cov : ⊙Cover X j) where
  cov = fst ⊙cov
  pt = snd ⊙cov
  open Cover cov public

-- Basics
module _ {A : Type i} {j} where

  open Cover

  -- Equality between covers.
  cover=' : {c₁ c₂ : Cover A j} → Fiber c₁ == Fiber c₂ → c₁ == c₂
  cover=' {cover f} {cover .f} idp = ap (λ (x : ∀ {a} → is-set (f a)) → cover f {{x}})
    (prop-has-all-paths _ _)

  cover= : {c₁ c₂ : Cover A j} → (∀ a → Fiber c₁ a ≃ Fiber c₂ a)
    → c₁ == c₂
  cover= F≃ = cover=' (λ= λ a → ua $ F≃ a)

  -- The definition of universality in terms of connectedness.
  is-universal : Cover A j → Type (lmax i j)
  is-universal cov = is-connected 1 $ TotalSpace cov

module _ (A : Type i) j where
  -- In terms of connectedness
  UniversalCover : Type (lmax i (lsucc j))
  UniversalCover = Σ (Cover A j) is-universal

module _ (X : Ptd i) j where
  -- In terms of connectedness
  ⊙UniversalCover : Type (lmax i (lsucc j))
  ⊙UniversalCover = Σ (⊙Cover X j) (λ ⊙cov → is-universal (fst ⊙cov))

module ⊙UniversalCover {X : Ptd i} {j} (⊙uc : ⊙UniversalCover X j) where
  ⊙cov = fst ⊙uc
  is-univ = snd ⊙uc
  open ⊙Cover ⊙cov public

-- Theorem: A covering space keeps higher homotopy groups.
module _ (X : Ptd i)
  {j} (c : Cover (de⊙ X) j)
  (a↑ : Cover.Fiber c (pt⊙ X)) where

  open Cover c
  private
    F = Cover.Fiber c
    A = de⊙ X
    a = pt⊙ X

  private
    -- The projection map with one end free (in order to apply J).
    to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
        → idp == p⇑ → idp == fst= p⇑
    to′ idp=p⇑ = ap fst= idp=p⇑

    -- The projection map from Ω²(Σ A F) to Ω²(A).
    to : Ω^ 2 ⊙[ Σ A F , (a , a↑) ] → Ω^ 2 X
    to p²⇑ = to′ {p⇑ = idp} p²⇑

    -- Auxiliary synthesized path for injection.
    idp=p↑ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
             → (idp=p : idp == p)
             → idp == p↑
               [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
    idp=p↑ idp = prop-has-all-paths _ _

    -- The injection map with some ends free (in order to apply J).
    from′ : ∀ {p : a == a} {p↑ : a↑ == a↑ [ F ↓ p ]}
            → (idp=p : idp == p)
            → idp == p↑ -- aux
              [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ idp=p ]
            → idp == pair= p p↑
    from′ idp=p idp=p↑ = pair== idp=p idp=p↑

    -- The injection map from Ω²(A) to Ω²(Σ A F).
    from : Ω^ 2 X → Ω^ 2 ⊙[ Σ A F , (a , a↑) ]
    from p² = from′ {p = idp} {p↑ = idp} p² (idp=p↑ p²)

    -- Injection is left-inverse to projection (with some ends free).
    from′-to′ : ∀ {p⇑ : _==_ {A = Σ A F} (a , a↑) (a , a↑)}
                → (idp=p⇑ : idp == p⇑)
                → (idp=snd=p⇑ : idp == snd= p⇑ -- aux
                  [ (λ p → a↑ == a↑ [ F ↓ p ]) ↓ to′ idp=p⇑ ])
                → from′ (to′ idp=p⇑) idp=snd=p⇑ == idp=p⇑
                  [ (λ p⇑ → idp == p⇑) ↓ ! (pair=-η p⇑) ]
    from′-to′ idp idp=snd=p⇑ = ap (from′ idp)
      $ contr-has-all-paths _ _

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
  Ω²ΣAFiber≃Ω²A : Ω^ 2 ⊙[ Σ A F , (a , a↑) ] ≃ Ω^ 2 X
  Ω²ΣAFiber≃Ω²A = to , is-eq to from to-from from-to

-- A natural way to construct a π1-set from covering spaces.
module _ {A : Type i} where
  open Cover

  cover-trace : ∀ {j} (cov : Cover A j) {a₁ a₂}
    → Fiber cov a₁ → a₁ =₀ a₂
    → Fiber cov a₂
  cover-trace cov a↑ p =
    transport₀ (Fiber cov) p a↑

  abstract
    cover-trace-idp₀ : ∀ {j} (cov : Cover A j) {a₁}
      → (a↑ : Fiber cov a₁)
      → cover-trace cov a↑ idp₀ == a↑
    cover-trace-idp₀ cov a↑ = idp

    cover-paste : ∀ {j} (cov : Cover A j) {a₁ a₂}
      → (a↑ : Fiber cov a₁)
      → (loop : a₁ =₀ a₁)
      → (p : a₁ =₀ a₂)
      → cover-trace cov (cover-trace cov a↑ loop) p
      == cover-trace cov a↑ (loop ∙₀ p)
    cover-paste cov a↑ loop p = ! $ transp₀-∙₀ loop p a↑

-- Path sets form a covering space
module _ (X : Ptd i) where
  path-set-cover : Cover (de⊙ X) i
  path-set-cover = record
    { Fiber = λ a → pt⊙ X =₀ a }

-- Cover morphisms
CoverHom : ∀ {A : Type i} {j₁ j₂}
  → (cov1 : Cover A j₁)
  → (cov2 : Cover A j₂)
  → Type (lmax i (lmax j₁ j₂))
CoverHom (cover F₁) (cover F₂) = ∀ a → F₁ a → F₂ a
