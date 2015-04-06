{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.elims.Lemmas where

↓-cancel : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y : A} {p : x == y}
  {u v : B x} {w : B y}
  (α : u == w [ B ↓ p ]) (β : v == w [ B ↓ p ])
  → u == v
↓-cancel {p = idp} α idp = α

↓-cancel-property : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y : A} {p : x == y}
  {u v : B x} {w : B y}
  (α : u == w [ B ↓ p ]) (β : v == w [ B ↓ p ])
  → α == (↓-cancel α β) ◃ β
↓-cancel-property {p = idp} idp idp = idp

↓-cancel-unique : ∀ {i j} {A : Type i} {B : A → Type j}
  {x y : A} {p : x == y}
  {u v : B x} {w : B y}
  (α : u == w [ B ↓ p ]) (β : v == w [ B ↓ p ]) (γ : u == v)
  → α == γ ◃ β → γ == ↓-cancel α β
↓-cancel-unique {p = idp} ._ idp idp idp = idp

↓↓-fill : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k}
  {x y : C → A} {u : (c : C) → B (x c)} {v : (c : C) → B (y c)}
  {p : (c : C) → x c == y c} {c₁ c₂ : C} (q : c₁ == c₂)
  (α : u c₁ == v c₁ [ B ↓ p c₁ ]) (β : u c₂ == v c₂ [ B ↓ p c₂ ])
  → Σ (u c₂ == u c₂)
      (λ γ → α == (γ ◃ β) [ (λ c → u c == v c [ B ↓ p c ]) ↓ q ])
↓↓-fill idp α β =
  (↓-cancel α β , ↓-cancel-property α β)

↓↓-fill-unique : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k}
  {x y : C → A} {u : (c : C) → B (x c)} {v : (c : C) → B (y c)}
  {p : (c : C) → x c == y c} {c₁ c₂ : C} (q : c₁ == c₂)
  (α : u c₁ == v c₁ [ B ↓ p c₁ ]) (β : u c₂ == v c₂ [ B ↓ p c₂ ])
  (γ : u c₂ == u c₂)
  → α == (γ ◃ β) [ (λ c → u c == v c [ B ↓ p c ]) ↓ q ]
  → γ == fst (↓↓-fill q α β)
↓↓-fill-unique idp α β γ = ↓-cancel-unique α β γ
