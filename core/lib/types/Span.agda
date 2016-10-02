{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.CommutingSquare

module lib.types.Span where

record Span {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor span
  field
    A : Type i
    B : Type j
    C : Type k
    f : C → A
    g : C → B

private
  span=-raw : ∀ {i j k} {A A' : Type i} (p : A == A')
    {B B' : Type j} (q : B == B') {C C' : Type k} (r : C == C')
    {f : C → A} {f' : C' → A'}
    (s : f == f' [ (λ CA → fst CA → snd CA) ↓ pair×= r p ])
    {g : C → B} {g' : C' → B'}
    (t : g == g' [ (λ CB → fst CB → snd CB) ↓ pair×= r q ])
    → (span A B C f g) == (span A' B' C' f' g')
  span=-raw idp idp idp idp idp = idp

abstract
  span= : ∀ {i j k} {A A' : Type i} (p : A ≃ A')
    {B B' : Type j} (q : B ≃ B') {C C' : Type k} (r : C ≃ C')
    {f : C → A} {f' : C' → A'} (s : (a : C) → (–> p) (f a) == f' (–> r a))
    {g : C → B} {g' : C' → B'} (t : (b : C) → (–> q) (g b) == g' (–> r b))
    → (span A B C f g) == (span A' B' C' f' g')
  span= p q r {f} {f'} s {g} {g'} t = span=-raw
    (ua p)
    (ua q)
    (ua r)
    (↓-→-in (λ α → ↓-snd×-in (ua r) (ua p) (↓-idf-ua-in p (
                   s _
                   ∙ ap f' (↓-idf-ua-out r (↓-fst×-out (ua r) (ua p) α))))))
    (↓-→-in (λ β → ↓-snd×-in (ua r) (ua q) (↓-idf-ua-in q (
                   t _
                   ∙ ap g' (↓-idf-ua-out r (↓-fst×-out (ua r) (ua q) β))))))

record ⊙Span {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ⊙span
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : Z ⊙→ X
    g : Z ⊙→ Y

⊙Span-to-Span : ∀ {i j k} → ⊙Span {i} {j} {k} → Span {i} {j} {k}
⊙Span-to-Span (⊙span X Y Z f g) = span (fst X) (fst Y) (fst Z) (fst f) (fst g)

{- Helper for path induction on pointed spans -}
⊙span-J : ∀ {i j k l} (P : ⊙Span {i} {j} {k} → Type l)
  → ({A : Type i} {B : Type j} {Z : Ptd k} (f : fst Z → A) (g : fst Z → B)
     → P (⊙span (A , f (snd Z)) (B , g (snd Z)) Z (f , idp) (g , idp)))
  → Π ⊙Span P
⊙span-J P t (⊙span (A , ._) (B , ._) Z (f , idp) (g , idp)) = t f g

{- Span-flipping functions -}
Span-flip : ∀ {i j k} → Span {i} {j} {k} → Span {j} {i} {k}
Span-flip (span A B C f g) = span B A C g f

⊙Span-flip : ∀ {i j k} → ⊙Span {i} {j} {k} → ⊙Span {j} {i} {k}
⊙Span-flip (⊙span X Y Z f g) = ⊙span Y X Z g f

record SpanMap {i₀ j₀ k₀ i₁ j₁ k₁} (span₀ : Span {i₀} {j₀} {k₀}) (span₁ : Span {i₁} {j₁} {k₁})
  : Type (lmax (lmax (lmax i₀ j₀) k₀) (lmax (lmax i₁ j₁) k₁)) where
  constructor span-map
  module span₀ = Span span₀
  module span₁ = Span span₁
  field
    hA : span₀.A → span₁.A
    hB : span₀.B → span₁.B
    hC : span₀.C → span₁.C
    f-commutes : CommSquare span₀.f span₁.f hC hA
    g-commutes : CommSquare span₀.g span₁.g hC hB

SpanEquiv : ∀ {i₀ j₀ k₀ i₁ j₁ k₁} (span₀ : Span {i₀} {j₀} {k₀}) (span₁ : Span {i₁} {j₁} {k₁})
  → Type (lmax (lmax (lmax i₀ j₀) k₀) (lmax (lmax i₁ j₁) k₁))
SpanEquiv span₀ span₁ = Σ (SpanMap span₀ span₁)
  (λ span-map → is-equiv (SpanMap.hA span-map)
              × is-equiv (SpanMap.hB span-map)
              × is-equiv (SpanMap.hC span-map))

SpanEquiv-inverse : ∀ {i₀ j₀ k₀ i₁ j₁ k₁} {span₀ : Span {i₀} {j₀} {k₀}} {span₁ : Span {i₁} {j₁} {k₁}}
  → SpanEquiv span₀ span₁ → SpanEquiv span₁ span₀
SpanEquiv-inverse (span-map hA hB hC f-commutes g-commutes , hA-ise , hB-ise , hC-ise)
  = ( span-map hA.g hB.g hC.g
      (CommSquare-inverse-v f-commutes hC-ise hA-ise)
      (CommSquare-inverse-v g-commutes hC-ise hB-ise)
    , ( is-equiv-inverse hA-ise
      , is-equiv-inverse hB-ise
      , is-equiv-inverse hC-ise))
  where module hA = is-equiv hA-ise
        module hB = is-equiv hB-ise
        module hC = is-equiv hC-ise
