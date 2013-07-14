{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Paths where

module _ {i j} {A : Type i} {B : Type j} {f : A → B} {b : B} where

  ↓-app='cst-in : {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙' v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app='cst-in {p = idp} q = q ∙ ∙'-unit-l _

  ↓-app='cst-out : {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙' v)
  ↓-app='cst-out {p = idp} idp = ! (∙'-unit-l _)

  ↓-cst='app-in : {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙' ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst='app-in {p = idp} idp = idp

  ↓-cst='app-out : {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙' ap f p) == v
  ↓-cst='app-out {p = idp} idp = idp

module _ {i} {A : Type i} {f : A → A} where

  ↓-app='idf-in : {x y : A} {p : x == y} {u : f x == x} {v : f y == y}
    → u ∙' p == ap f p ∙ v
    → u == v [ (λ z → f z == z) ↓ p ]
  ↓-app='idf-in {p = idp} q = q

↓-cst=idf-in : ∀ {i} {A : Type i} {a : A}
  {x y : A} {p : x == y} {u : a == x} {v : a == y}
  → (u ∙ p) == v
  → (u == v [ (λ x → a == x) ↓ p ])
↓-cst=idf-in {p = idp} q = ! (∙-unit-r _) ∙ q

↓-idf=cst-in : ∀ {i} {A : Type i} {a : A}
  {x y : A} {p : x == y} {u : x == a} {v : y == a}
  → u == p ∙' v
  → (u == v [ (λ x → x == a) ↓ p ])
↓-idf=cst-in {p = idp} q = q ∙ ∙'-unit-l _

↓-idf=idf-in : ∀ {i} {A : Type i}
  {x y : A} {p : x == y} {u : x == x} {v : y == y}
  → u ∙ p == p ∙' v
  → (u == v [ (λ x → x == x) ↓ p ])
↓-idf=idf-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ ∙'-unit-l _


↓-='-in : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → (u ∙ ap g p) == (ap f p ∙' v)
  → (u == v [ (λ x → f x == g x) ↓ p ])
↓-='-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ (∙'-unit-l _)

-- Dependent vs nondependent whiskering
-- This definitional behaviour make [↓-=-in] slightly more complicated to prove
-- but [↓-=-in] is often used in the case where [u] and [v] are [idp]

↓-=-in : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u ◃ apd f p) == (apd g p ▹ v)
  → (u == v [ (λ x → g x == f x) ↓ p ])
↓-=-in {B = B} {p = idp} {u} {v} q = ! (◃idp u) ∙ q ∙ idp▹ v

postulate
 ↓-=-out : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u == v [ (λ x → g x == f x) ↓ p ])
  → (u ◃ apd f p) == (apd g p ▹ v)
--↓-=-out {B = B} {p = idp} idp = {!!}

-- Dependent path in a type of the form [λ x → g (f x) ≡ x]
module _ {i j} {A : Type i} {B : Type j} (f : A → B) (g : B → A) where
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
