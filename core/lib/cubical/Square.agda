{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.PathOver

module lib.cubical.Square where

{-
  *--1--*
  |     |
  0     3
  |     |
  *--2--*
-}

data Square {i} {A : Type i} {a₀₀ : A} : {a₀₁ a₁₀ a₁₁ : A}
  → a₀₀ == a₀₁ → a₀₀ == a₁₀ → a₀₁ == a₁₁ → a₁₀ == a₁₁ → Type i
  where
  ids : Square idp idp idp idp

hid-square : ∀ {i} {A : Type i} {a₀₀ a₀₁ : A} {p : a₀₀ == a₀₁}
  → Square p idp idp p
hid-square {p = idp} = ids

vid-square : ∀ {i} {A : Type i} {a₀₀ a₁₀ : A} {p : a₀₀ == a₁₀}
  → Square idp p p idp
vid-square {p = idp} = ids

square-to-disc : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → p₀₋ ∙ p₋₁ == p₋₀ ∙ p₁₋
square-to-disc ids = idp

disc-to-square : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → p₀₋ ∙ p₋₁ == p₋₀ ∙ p₁₋
  → Square p₀₋ p₋₀ p₋₁ p₁₋
disc-to-square {p₀₋ = idp} {p₋₀ = idp} {p₋₁ = idp} {p₁₋ = .idp} idp = ids

square-to-disc-β : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (α : p₀₋ ∙ p₋₁ == p₋₀ ∙ p₁₋)
  → square-to-disc (disc-to-square {p₀₋ = p₀₋} {p₋₀ = p₋₀} α) == α
square-to-disc-β {p₀₋ = idp} {p₋₀ = idp} {p₋₁ = idp} {p₁₋ = .idp} idp = idp

disc-to-square-β : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → disc-to-square (square-to-disc sq) == sq
disc-to-square-β ids = idp


ap-square : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square (ap f p₀₋) (ap f p₋₀) (ap f p₋₁) (ap f p₁₋)
ap-square f ids = ids

ap-square-hid : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  {a₀ a₁ : A} {p : a₀ == a₁}
  → ap-square f (hid-square {p = p}) == hid-square
ap-square-hid {p = idp} = idp

ap-square-vid : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  {a₀ a₁ : A} {p : a₀ == a₁}
  → ap-square f (vid-square {p = p}) == vid-square
ap-square-vid {p = idp} = idp


module _ {i} {A : Type i} where

  horiz-degen-square : {a a' : A} {p q : a == a'}
    → p == q → Square p idp idp q
  horiz-degen-square {p = idp} α = disc-to-square α

  horiz-degen-path : {a a' : A} {p q : a == a'}
    → Square p idp idp q → p == q
  horiz-degen-path {p = idp} sq = square-to-disc sq

  horiz-degen-path-β : {a a' : A} {p q : a == a'} (α : p == q)
    → horiz-degen-path (horiz-degen-square α) == α
  horiz-degen-path-β {p = idp} α = square-to-disc-β α

  horiz-degen-square-β : {a a' : A} {p q : a == a'} (sq : Square p idp idp q)
    → horiz-degen-square (horiz-degen-path sq) == sq
  horiz-degen-square-β {p = idp} sq = disc-to-square-β sq

  vert-degen-square : {a a' : A} {p q : a == a'}
    → p == q → Square idp p q idp
  vert-degen-square {p = idp} α = disc-to-square (! α)

  vert-degen-path : {a a' : A} {p q : a == a'}
    → Square idp p q idp → p == q
  vert-degen-path {p = idp} sq = ! (square-to-disc sq)

  vert-degen-path-β : {a a' : A} {p q : a == a'} (α : p == q)
    → vert-degen-path (vert-degen-square α) == α
  vert-degen-path-β {p = idp} α = ap ! (square-to-disc-β (! α)) ∙ !-! α

  vert-degen-square-β : {a a' : A} {p q : a == a'} (sq : Square idp p q idp)
    → vert-degen-square (vert-degen-path sq) == sq
  vert-degen-square-β {p = idp} sq =
    ap disc-to-square (!-! (square-to-disc sq)) ∙ disc-to-square-β sq


  horiz-degen-square-idp : {a a' : A} {p : a == a'}
    → horiz-degen-square (idp {a = p}) == hid-square
  horiz-degen-square-idp {p = idp} = idp

  vert-degen-square-idp : {a a' : A} {p : a == a'}
    → vert-degen-square (idp {a = p}) == vid-square
  vert-degen-square-idp {p = idp} = idp

{- Flipping squares -}
module _ {i} {A : Type i} where

  square-symmetry : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₋₀ p₀₋ p₁₋ p₋₁
  square-symmetry ids = ids

  square-sym-inv : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → square-symmetry (square-symmetry sq) == sq
  square-sym-inv ids = idp

ap-square-symmetry : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → ap-square f (square-symmetry sq) == square-symmetry (ap-square f sq)
ap-square-symmetry f ids = idp

{- Alternate induction principles -}

square-left-J : ∀ {i j} {A : Type i} {a₀₀ a₀₁ : A} {p₀₋ : a₀₀ == a₀₁}
  (P : {a₁₀ a₁₁ : A} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
       (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
       → Type j)
  (r : P hid-square)
  {a₁₀ a₁₁ : A} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → P sq
square-left-J P r ids = r

square-top-J : ∀ {i j} {A : Type i} {a₀₀ a₁₀ : A} {p₋₀ : a₀₀ == a₁₀}
  (P : {a₀₁ a₁₁ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
       (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
       → Type j)
  (r : P vid-square)
  {a₀₁ a₁₁ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → P sq
square-top-J P r ids = r

square-bot-J : ∀ {i j} {A : Type i} {a₀₁ a₁₁ : A} {p₋₁ : a₀₁ == a₁₁}
  (P : {a₀₀ a₁₀ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₁₋ : a₁₀ == a₁₁}
       (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
       → Type j)
  (r : P vid-square)
  {a₀₀ a₁₀ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → P sq
square-bot-J P r ids = r

square-right-J : ∀ {i j} {A : Type i} {a₁₀ a₁₁ : A} {p₁₋ : a₁₀ == a₁₁}
  (P : {a₀₀ a₀₁ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁}
       (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
       → Type j)
  (r : P hid-square)
  {a₀₀ a₀₁ : A} {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → P sq
square-right-J P r ids = r

module _ where
  private
    lemma : ∀ {i j} {A : Type i} {a₀ : A}
      (P : {a₁ : A} {p q : a₀ == a₁} → p == q → Type j)
      (r : P (idp {a = idp}))
      {a₁ : A} {p q : a₀ == a₁} (α : p == q)
      → P α
    lemma P r {p = idp} idp = r

  horiz-degen-J : ∀ {i j} {A : Type i} {a₀ : A}
    (P : {a₁ : A} {p q : a₀ == a₁} → Square p idp idp q → Type j)
    (r : P ids)
    {a₁ : A} {p q : a₀ == a₁} (sq : Square p idp idp q)
    → P sq
  horiz-degen-J P r sq = transport P
    (horiz-degen-square-β sq)
    (lemma (P ∘ horiz-degen-square) r (horiz-degen-path sq))

  vert-degen-J : ∀ {i j} {A : Type i} {a₀ : A}
    (P : {a₁ : A} {p q : a₀ == a₁} → Square idp p q idp → Type j)
    (r : P ids)
    {a₁ : A} {p q : a₀ == a₁} (sq : Square idp p q idp)
    → P sq
  vert-degen-J P r sq = transport P
    (vert-degen-square-β sq)
    (lemma (P ∘ vert-degen-square) r (vert-degen-path sq))

{- Square filling -}
module _ {i} {A : Type i} where
  fill-square-left : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (p₋₀ : a₀₀ == a₁₀) (p₋₁ : a₀₁ == a₁₁) (p₁₋ : a₁₀ == a₁₁)
    → Σ (a₀₀ == a₀₁) (λ p₀₋ → Square p₀₋ p₋₀ p₋₁ p₁₋)
  fill-square-left idp idp p = (p , hid-square)

  fill-square-top : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (p₀₋ : a₀₀ == a₀₁) (p₋₁ : a₀₁ == a₁₁) (p₁₋ : a₁₀ == a₁₁)
    → Σ (a₀₀ == a₁₀) (λ p₋₀ → Square p₀₋ p₋₀ p₋₁ p₁₋)
  fill-square-top idp p idp = (p , vid-square)

  fill-square-bot : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (p₀₋ : a₀₀ == a₀₁) (p₋₀ : a₀₀ == a₁₀) (p₁₋ : a₁₀ == a₁₁)
    → Σ (a₀₁ == a₁₁) (λ p₋₁ → Square p₀₋ p₋₀ p₋₁ p₁₋)
  fill-square-bot idp p idp = (p , vid-square)

  fill-square-right : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    (p₀₋ : a₀₀ == a₀₁) (p₋₀ : a₀₀ == a₁₀) (p₋₁ : a₀₁ == a₁₁)
    → Σ (a₁₀ == a₁₁) (λ p₁₋ → Square p₀₋ p₋₀ p₋₁ p₁₋)
  fill-square-right p idp idp = (p , hid-square)

module _  {i j} {A : Type i} {B : Type j} {f : A → B} {b : B} where

  ↓-cst=app-from-square : {x y : A} {p : x == y}
    {u : b == f x} {v : b == f y}
    → Square u idp (ap f p) v
    → u == v [ (λ z → b == f z) ↓ p ]
  ↓-cst=app-from-square {p = idp} sq = horiz-degen-path sq

  ↓-cst=app-to-square : {x y : A} {p : x == y}
    {u : b == f x} {v : b == f y}
    → u == v [ (λ z → b == f z) ↓ p ]
    → Square u idp (ap f p) v
  ↓-cst=app-to-square {p = idp} α = horiz-degen-square α

  ↓-app=cst-from-square : {x y : A} {p : x == y}
    {u : f x == b} {v : f y == b}
    → Square u (ap f p) idp v
    → u == v [ (λ z → f z == b) ↓ p ]
  ↓-app=cst-from-square {p = idp} sq = horiz-degen-path sq

  ↓-app=cst-to-square : {x y : A} {p : x == y}
    {u : f x == b} {v : f y == b}
    → u == v [ (λ z → f z == b) ↓ p ]
    → Square u (ap f p) idp v
  ↓-app=cst-to-square {p = idp} α = horiz-degen-square α

module _  {i} {A : Type i} {f : A → A} where

  ↓-idf=app-from-square : {x y : A} {p : x == y}
    {u : x == f x} {v : y == f y}
    → Square u p (ap f p) v
    → u == v [ (λ z → z == f z) ↓ p ]
  ↓-idf=app-from-square {p = idp} sq = horiz-degen-path sq

  ↓-idf=app-to-square : {x y : A} {p : x == y}
    {u : x == f x} {v : y == f y}
    → u == v [ (λ z → z == f z) ↓ p ]
    → Square u p (ap f p) v
  ↓-idf=app-to-square {p = idp} α = horiz-degen-square α

  ↓-app=idf-from-square : {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → Square u (ap f p) p v
    → u == v [ (λ z → f z == z) ↓ p ]
  ↓-app=idf-from-square {p = idp} sq = horiz-degen-path sq

  ↓-app=idf-to-square : {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u == v [ (λ z → f z == z) ↓ p ]
    → Square u (ap f p) p v
  ↓-app=idf-to-square {p = idp} α = horiz-degen-square α

module _  {i j} {A : Type i} {B : Type j} (g : B → A) (f : A → B) where

  ↓-∘=idf-from-square : {x y : A} {p : x == y}
    {u : g (f x) == x} {v : g (f y) == y}
    → Square u (ap g (ap f p)) p v
    → (u == v [ (λ z → g (f z) == z) ↓ p ])
  ↓-∘=idf-from-square {p = idp} sq = horiz-degen-path sq

  ↓-∘=idf-to-square : {x y : A} {p : x == y}
    {u : g (f x) == x} {v : g (f y) == y}
    → (u == v [ (λ z → g (f z) == z) ↓ p ])
    → Square u (ap g (ap f p)) p v
  ↓-∘=idf-to-square {p = idp} α = horiz-degen-square α

_⊡v_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {q₀₋ : a₀₁ == a₀₂} {q₋₂ : a₀₂ == a₁₂} {q₁₋ : a₁₁ == a₁₂}
  → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square q₀₋ p₋₁ q₋₂ q₁₋
  → Square (p₀₋ ∙ q₀₋) p₋₀ q₋₂ (p₁₋ ∙ q₁₋)
ids ⊡v sq = sq

_⊡v'_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {q₀₋ : a₀₁ == a₀₂} {q₋₂ : a₀₂ == a₁₂} {q₁₋ : a₁₁ == a₁₂}
  → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square q₀₋ p₋₁ q₋₂ q₁₋
  → Square (p₀₋ ∙' q₀₋) p₋₀ q₋₂ (p₁₋ ∙' q₁₋)
sq ⊡v' ids = sq

_∙v⊡_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ p₋₀' : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → p₋₀ == p₋₀'
  → Square p₀₋ p₋₀' p₋₁ p₁₋
  → Square p₀₋ p₋₀ p₋₁ p₁₋
idp ∙v⊡ sq = sq

_⊡v∙_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₋₀ : a₀₀ == a₁₀} {p₀₋ : a₀₀ == a₀₁}
  {p₋₁ p₋₁' : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → p₋₁ == p₋₁'
  → Square p₀₋ p₋₀ p₋₁' p₁₋
sq ⊡v∙ idp = sq

_⊡h_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₂₀ a₂₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {q₋₀ : a₁₀ == a₂₀} {q₋₁ : a₁₁ == a₂₁} {q₂₋ : a₂₀ == a₂₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square p₁₋ q₋₀ q₋₁ q₂₋
  → Square p₀₋ (p₋₀ ∙ q₋₀) (p₋₁ ∙ q₋₁) q₂₋
ids ⊡h sq = sq

_⊡h'_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₂₀ a₂₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {q₋₀ : a₁₀ == a₂₀} {q₋₁ : a₁₁ == a₂₁} {q₂₋ : a₂₀ == a₂₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square p₁₋ q₋₀ q₋₁ q₂₋
  → Square p₀₋ (p₋₀ ∙' q₋₀) (p₋₁ ∙' q₋₁) q₂₋
sq ⊡h' ids = sq

_∙h⊡_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ p₀₋' : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  → p₀₋ == p₀₋'
  → Square p₀₋' p₋₀ p₋₁ p₁₋
  → Square p₀₋ p₋₀ p₋₁ p₁₋
idp ∙h⊡ sq = sq

_⊡h∙_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ p₁₋' : a₁₀ == a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → p₁₋ == p₁₋'
  → Square p₀₋ p₋₀ p₋₁ p₁₋'
sq ⊡h∙ idp = sq

infixr 80 _⊡v_ _⊡v'_ _⊡h_ _⊡h'_

infixr 80 _∙v⊡_ _∙h⊡_
infixl 85 _⊡v∙_ _⊡h∙_

∙v⊡-assoc : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₋₀ p₋₀' p₋₀'' : a₀₀ == a₁₀} {p₀₋ : a₀₀ == a₀₁}
  {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (q : p₋₀ == p₋₀')
  (r : p₋₀' == p₋₀'')
  (sq : Square p₀₋ p₋₀'' p₋₁ p₁₋)
  → (q ∙ r) ∙v⊡ sq == q ∙v⊡ (r ∙v⊡ sq)
∙v⊡-assoc q@idp r sq = idp

⊡v∙-assoc : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₋₀ : a₀₀ == a₁₀} {p₀₋ : a₀₀ == a₀₁}
  {p₋₁ p₋₁' p₋₁'' : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  (q : p₋₁ == p₋₁')
  (r : p₋₁' == p₋₁'')
  → (sq ⊡v∙ q) ⊡v∙ r == sq ⊡v∙ (q ∙ r)
⊡v∙-assoc sq q@idp r = idp

∙v⊡-⊡v∙-comm : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₋₀ p₋₀' : a₀₀ == a₁₀} {p₀₋ : a₀₀ == a₀₁}
  {p₋₁ p₋₁' : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (q : p₋₀ == p₋₀')
  (sq : Square p₀₋ p₋₀' p₋₁ p₁₋)
  (r : p₋₁ == p₋₁')
  → (q ∙v⊡ sq) ⊡v∙ r == q ∙v⊡ (sq ⊡v∙ r)
∙v⊡-⊡v∙-comm q@idp sq r = idp

⊡h-⊡v∙-comm : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₂₀ a₂₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ p₋₁' : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {q₋₀ : a₁₀ == a₂₀} {q₋₁ q₋₁' : a₁₁ == a₂₁} {q₂₋ : a₂₀ == a₂₁}
  (p-sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  (q-sq : Square p₁₋ q₋₀ q₋₁ q₂₋)
  (r : p₋₁ == p₋₁')
  (s : q₋₁ == q₋₁')
  → (p-sq ⊡h q-sq) ⊡v∙ (ap2 _∙_ r s) == (p-sq ⊡v∙ r) ⊡h (q-sq ⊡v∙ s)
⊡h-⊡v∙-comm p-sq q-sq r@idp s@idp = idp

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  ↓-='-to-square : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → u == v [ (λ z → f z == g z) ↓ p ]
    → Square u (ap f p) (ap g p) v
  ↓-='-to-square {p = idp} α = horiz-degen-square α

  ↓-='-from-square : {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → Square u (ap f p) (ap g p) v
    → u == v [ (λ z → f z == g z) ↓ p ]
  ↓-='-from-square {p = idp} sq = horiz-degen-path sq

  ↓-='-square-comp : {x y z : A} {p : x == y} {q : y == z}
    {u : f x == g x} {v : f y == g y} {w : f z == g z}
    → Square u (ap f p) (ap g p) v
    → Square v (ap f q) (ap g q) w
    → Square u (ap f (p ∙ q)) (ap g (p ∙ q)) w
  ↓-='-square-comp {p = idp} {q = idp} sq₁ sq₂ =
    horiz-degen-square (horiz-degen-path sq₁ ∙ horiz-degen-path sq₂)

  ↓-='-from-square-comp : {x y z : A} {p : x == y} {q : y == z}
    {u : f x == g x} {v : f y == g y} {w : f z == g z}
    (sq₁ : Square u (ap f p) (ap g p) v)
    (sq₂ : Square v (ap f q) (ap g q) w)
    → ↓-='-from-square (↓-='-square-comp sq₁ sq₂) ==
      ↓-='-from-square sq₁ ∙ᵈ ↓-='-from-square sq₂
  ↓-='-from-square-comp {p = idp} {q = idp} sq₁ sq₂ =
    horiz-degen-path-β _

  private
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

  ↓-='-from-square-comp-path :
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
  ↓-='-from-square-comp-path comp p-sq q-sq r-sq e =
    ap↓ ↓-='-from-square (custom-square-over comp p-sq q-sq r-sq e) ▹
    ↓-='-from-square-comp p-sq q-sq

module _ {i j} {A : Type i} {B : Type j} where

  natural-square : {f₁ f₂ : A → B} (p : ∀ a → f₁ a == f₂ a)
    {a₁ a₂ : A} (q : a₁ == a₂)
    → Square (p a₁) (ap f₁ q) (ap f₂ q) (p a₂)
  natural-square p idp = hid-square

  natural-square-idp : {f₁ : A → B} {a₁ a₂ : A} (q : a₁ == a₂)
    → natural-square {f₁ = f₁} (λ _ → idp) q == vid-square
  natural-square-idp idp = idp

  {- Used for getting square equivalents of glue-β terms -}
  natural-square-β : {f₁ f₂ : A → B} (p : (a : A) → f₁ a == f₂ a)
    {x y : A} (q : x == y)
    {sq : Square (p x) (ap f₁ q) (ap f₂ q) (p y)}
    → apd p q == ↓-='-from-square sq
    → natural-square p q == sq
  natural-square-β _ idp α =
    ! horiz-degen-square-idp ∙ ap horiz-degen-square α ∙ horiz-degen-square-β _

module _ {i} {A : Type i} where

  horiz-degen-path-⊡h : {a a' : A} {p q r : a == a'}
    (sq₁ : Square p idp idp q)
    (sq₂ : Square q idp idp r)
    → horiz-degen-path (sq₁ ⊡h sq₂) ==
      horiz-degen-path sq₁ ∙ horiz-degen-path sq₂
  horiz-degen-path-⊡h {p = idp} {q = .idp} ids sq₂ = idp

  vert-degen-square-⊡v∙ : {a a' : A} {p q r : a == a'}
    → (s : p == q) (t : q == r)
    → vert-degen-square s ⊡v∙ t == vert-degen-square (s ∙ t)
  vert-degen-square-⊡v∙ idp idp = idp

  vert-degen-square-∙v⊡ : {a a' : A} {p q r : a == a'}
    → (s : p == q) (t : q == r)
    → s ∙v⊡ vert-degen-square t == vert-degen-square (s ∙ t)
  vert-degen-square-∙v⊡ idp idp = idp

  vert-degen-square-⊡h : {a a' a'' : A}
    {p p' : a == a'} {q q' : a' == a''}
    (s : p == p') (t : q == q')
    → vert-degen-square s ⊡h vert-degen-square t ==
      vert-degen-square (ap2 _∙_ s t)
  vert-degen-square-⊡h {p = idp} idp idp = idp

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  ↓-='-square-comp' : {x y z : A} {p : x == y} {q : y == z}
    {u : f x == g x} {v : f y == g y} {w : f z == g z}
    → Square u (ap f p) (ap g p) v
    → Square v (ap f q) (ap g q) w
    → Square u (ap f (p ∙ q)) (ap g (p ∙ q)) w
  ↓-='-square-comp' {p = p} {q = q} sq₁ sq₂ =
    ap-∙ f p q ∙v⊡ ((sq₁ ⊡h sq₂) ⊡v∙ ∙-ap g p q)

  ↓-='-square-comp'=↓-='-square-comp : {x y z : A} {p : x == y} {q : y == z}
    {u : f x == g x} {v : f y == g y} {w : f z == g z}
    → (sq₁ : Square u (ap f p) (ap g p) v)
    → (sq₂ : Square v (ap f q) (ap g q) w)
    → ↓-='-square-comp' sq₁ sq₂ == ↓-='-square-comp sq₁ sq₂
  ↓-='-square-comp'=↓-='-square-comp {p = idp} {q = idp} sq₁ sq₂ =
    ↓-='-square-comp' sq₁ sq₂
      =⟨ idp ⟩
    sq₁ ⊡h sq₂
      =⟨ ! (horiz-degen-square-β (sq₁ ⊡h sq₂)) ⟩
    horiz-degen-square (horiz-degen-path (sq₁ ⊡h sq₂))
      =⟨ ap horiz-degen-square (horiz-degen-path-⊡h sq₁ sq₂) ⟩
    horiz-degen-square (horiz-degen-path sq₁ ∙ horiz-degen-path sq₂) =∎

module _ {i} {A : Type i} where
  !□h : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋
    → Square p₁₋ (! p₋₀) (! p₋₁) p₀₋
  !□h ids = ids

  !□v : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋
    → Square (! p₀₋) p₋₁ p₋₀ (! p₁₋)
  !□v ids = ids

module _ {i} {A : Type i} where

  {- TODO rest of these -}

  ⊡h-unit-l : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → hid-square ⊡h sq == sq
  ⊡h-unit-l ids = idp

  ⊡h-unit-r : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → sq ⊡h hid-square == ∙-unit-r _ ∙v⊡ (sq ⊡v∙ ! (∙-unit-r _))
  ⊡h-unit-r ids = idp

  ⊡h'-unit-l : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → hid-square ⊡h' sq == ∙'-unit-l _ ∙v⊡ (sq ⊡v∙ ! (∙'-unit-l _))
  ⊡h'-unit-l ids = idp

  ⊡h-unit-l-unique : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq' : Square p₀₋ idp idp p₀₋) (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → sq' ⊡h sq == sq
    → sq' == hid-square
  ⊡h-unit-l-unique sq' ids p = ! (⊡h-unit-r sq') ∙ p


module _ {i} {A : Type i} where
  !□h-inv-l : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → (!□h sq) ⊡h sq == !-inv-l p₋₀ ∙v⊡ (hid-square ⊡v∙ ! (!-inv-l p₋₁))
  !□h-inv-l ids = idp

  !□h-inv-r : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → sq ⊡h (!□h sq) == !-inv-r p₋₀ ∙v⊡ (hid-square ⊡v∙ ! (!-inv-r p₋₁))
  !□h-inv-r ids = idp

  !□v-inv-l : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → (!□v sq) ⊡v sq == !-inv-l p₀₋ ∙h⊡ (vid-square ⊡h∙ ! (!-inv-l p₁₋))
  !□v-inv-l ids = idp

  !□v-inv-r : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
    → sq ⊡v (!□v sq) == !-inv-r p₀₋ ∙h⊡ (vid-square ⊡h∙ ! (!-inv-r p₁₋))
  !□v-inv-r ids = idp

module _ {i} {A : Type i} where
  square-left-unique : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ p₀₋' : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₀₋' p₋₀ p₋₁ p₁₋
    → p₀₋ == p₀₋'
  square-left-unique {p₋₀ = idp} {p₋₁ = idp} sq₁ sq₂ =
    horiz-degen-path (sq₁ ⊡h (!□h sq₂))

  square-top-unique : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ p₋₀' : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₀₋ p₋₀' p₋₁ p₁₋
    → p₋₀ == p₋₀'
  square-top-unique {p₀₋ = idp} {p₁₋ = idp} sq₁ sq₂ =
    vert-degen-path (sq₁ ⊡v (!□v sq₂))

  square-bot-unique : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ p₋₁' : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₀₋ p₋₀ p₋₁' p₁₋
    → p₋₁ == p₋₁'
  square-bot-unique {p₀₋ = idp} {p₁₋ = idp} sq₁ sq₂ =
    vert-degen-path ((!□v sq₁) ⊡v sq₂)

  square-right-unique : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
    {p₋₁ : a₀₁ == a₁₁} {p₁₋ p₁₋' : a₁₀ == a₁₁}
    → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square p₀₋ p₋₀ p₋₁ p₁₋'
    → p₁₋ == p₁₋'
  square-right-unique {p₋₀ = idp} {p₋₁ = idp} sq₁ sq₂ =
    horiz-degen-path ((!□h sq₁) ⊡h sq₂)

module _ {i} {A : Type i} where

  {- XXX naminig -}
  connection : {a₀ a₁ : A} {q : a₀ == a₁}
    → Square idp idp q q
  connection {q = idp} = ids

  {- XXX naminig -}
  connection2 : {a₀ a₁ a₂ : A} {p : a₀ == a₁} {q : a₁ == a₂}
    → Square p p q q
  connection2 {p = idp} {q = idp} = ids

  lb-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square p idp (! p) idp
  lb-square idp = ids

  bl-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square (! p) idp p idp
  bl-square idp = ids

  br-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square idp idp p p
  br-square idp = ids

  rb-square = br-square

  rt-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square idp (! p) idp p
  rt-square idp = ids

  tr-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square idp p idp (! p)
  tr-square idp = ids

  lt-square : {a₀ a₁ : A} (p : a₀ == a₁)
    → Square p p idp idp
  lt-square idp = ids

  tl-square = lt-square
