{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Paths where

↓-app='cst-in : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
  → u == (ap f p ∙' v)
  → (u == v [ (λ x → f x == b) ↓ p ])
↓-app='cst-in {p = idp} q = q ∙ ∙'-unit-l _

↓-app='cst-out : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
  → (u == v [ (λ x → f x == b) ↓ p ])
  → u == (ap f p ∙' v)
↓-app='cst-out {p = idp} idp = ! (∙'-unit-l _)

↓-cst='app-in : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
  → (u ∙' ap f p) == v
  → (u == v [ (λ x → b == f x) ↓ p ])
↓-cst='app-in {p = idp} idp = idp

↓-cst='app-out : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
  → (u == v [ (λ x → b == f x) ↓ p ])
  → (u ∙' ap f p) == v
↓-cst='app-out {p = idp} idp = idp

↓-cst=idf-in : ∀ {i} {A : Set i} {a : A}
  {x y : A} {p : x == y} {u : a == x} {v : a == y}
  → (u ∙ p) == v
  → (u == v [ (λ x → a == x) ↓ p ])
↓-cst=idf-in {p = idp} idp = ! (∙-unit-r _)

↓-idf=idf-in : ∀ {i} {A : Set i}
  {x y : A} {p : x == y} {u : x == x} {v : y == y}
  → u ∙ p == p ∙' v
  → (u == v [ (λ x → x == x) ↓ p ])
↓-idf=idf-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ ∙'-unit-l _


↓-='-in : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → (u ∙ ap g p) == (ap f p ∙' v)
  → (u == v [ (λ x → f x == g x) ↓ p ])
↓-='-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ (∙'-unit-l _)

-- Dependent vs nondependent whiskering
-- This definitional behaviour make [↓-=-in] slightly more complicated to prove
-- but [↓-=-in] is often used in the case where [u] and [v] are [idp]
_▹_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u : B x}
  {v w : B y} {p : x == y}
  → (u == v [ B ↓ p ]) → v == w
     → (u == w [ B ↓ p ])
_▹_ {p = idp} q idp = q

idp▹ : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v == w)
  → _▹_ {B = B} {p = idp} idp q == q
idp▹ idp = idp

_◃_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u v : B x}
  {w : B y} {p : x == y}
  → (u == v → (v == w [ B ↓ p ])
     → (u == w [ B ↓ p ]))
_◃_ {p = idp} idp q = q

◃idp : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v == w)
  → _◃_ {B = B} {p = idp} q idp == q
◃idp idp = idp


↓-=-in : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u ◃ apd f p) == (apd g p ▹ v)
  → (u == v [ (λ x → g x == f x) ↓ p ])
↓-=-in {B = B} {p = idp} {u} {v} q =
  ! (◃idp {B = B} u) ∙ (q ∙ idp▹ {B = B} v)

postulate
 ↓-=-out : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u == v [ (λ x → g x == f x) ↓ p ])
  → (u ◃ apd f p) == (apd g p ▹ v)
--↓-=-out {B = B} {p = idp} idp = {!!}

-- Dependent path in a type of the form [λ x → g (f x) ≡ x]
module _ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) where
  ↓-∘=id-in : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → ((ap g (ap f p) ∙' v) == (u ∙ p))
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-∘=id-in {p = idp} q = ! (∙-unit-r _) ∙ (! q) ∙ (∙'-unit-l _)

-- WIP, derive it from more primitive principles
-- ↓-∘≡id-in f g {p = p} {u} {v} q =
--   ↓-≡-in (u ◃ apd (λ x → g (f x)) p =⟨ apd-∘ f g p |in-ctx (λ t → u ◃ t) ⟩
--         u ◃ ↓-apd-out _ f p (apdd g p (apd f p)) =⟨ apdd-cst (λ _ b → g b) p (ap f p) (! (apd-nd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (apd (λ t → g (π₂ t)) (pair= p (apd f p))) =⟨ apd-∘ π₂ g (pair= p (apd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (↓-apd-out _ π₂ (pair= p (apd f p)) (apdd g (pair= p (apd f p)) (apd π₂ (pair= p (apd f p))))) =⟨ {!!} ⟩
--         apd (λ x → x) p ▹ v ∎)
