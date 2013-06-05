{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Funext
open import lib.Equivalences
open import lib.Univalence
open import lib.PathGroupoid

module lib.PathOver where

-- Dependent paths in a constant fibration
module _ {i j} {A : Set i} {B : Set j} where

  ↓-cst-in : {x y : A} {p : x == y} {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in {p = idp} q = q

  ↓-cst-out : {x y : A} {p : x == y} {u v : B}
    → u == v [ (λ _ → B) ↓ p ]
    → u == v
  ↓-cst-out {p = idp} q = q

  ↓-cst-β : {x y : A} (p : x == y) {u v : B} (q : u == v)
    → (↓-cst-out (↓-cst-in {p = p} q) == q)
  ↓-cst-β idp q = idp

  ↓-cst-in-∙ : {x y z : A} (p : x == y) (q : y == z) {u v w : B}
    (p' : u == v) (q' : v == w)
    → ↓-cst-in {p = p} p' ∙dep ↓-cst-in {p = q} q'
    == ↓-cst-in {p = p ∙ q} (p' ∙ q')
  ↓-cst-in-∙ idp idp idp idp = idp

  ↓-cst-in2 : {a a' : A} {u v : B}
    {p₀ : a == a'} {p₁ : a == a'} {q₀ q₁ : u == v} {q : p₀ == p₁}
    → q₀ == q₁
    → (↓-cst-in {p = p₀} q₀ == ↓-cst-in {p = p₁} q₁ [ (λ p → u == v [ (λ _ → B) ↓ p ]) ↓ q ])
  ↓-cst-in2 {p₀ = idp} {p₁ = .idp} {q₀} {q₁} {idp} k = k

-- Dependent paths in a fibration constant in the second argument
module _ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k} where

  ↓-cst2-in : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ]
  ↓-cst2-in idp idp r = r

  ↓-cst2-out : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ]
    → u == v [ B ↓ p ]
  ↓-cst2-out idp idp r = r

-- Dependent paths in a fibration constant and non dependent in the
-- second argument
module _ {i j k} {A : Set i} {B : A → Set j} {C : Set k} where

  ↓-cst2'-in : {x y : A} (p : x == y) {b c : C}
    (q : b == c) {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → u == v [ (λ xy → B (fst xy)) ↓ (pair=' p q) ]
  ↓-cst2'-in idp idp r = r

  ↓-cst2'-out : {x y : A} (p : x == y) {b c : C}
    (q : b == c) {u : B x} {v : B y}
    → u == v [ (λ xy → B (fst xy)) ↓ (pair=' p q) ]
    → u == v [ B ↓ p ]
  ↓-cst2'-out idp idp r = r

-- -- ap can be defined via apd, not sure whether it’s a good idea or not
-- ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A} (p : x == y)
--   → f x == f y
-- ap f p = ↓-cst-out (apd f p)

apd=cst-in : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  {a a' : A} {p : a == a'} {q : f a == f a'}
  → apd f p == ↓-cst-in q → ap f p == q
apd=cst-in {p = idp} x = x

↓-apd-out : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k)
  {f : Π A B} {x y : A} {p : x == y}
  {q : f x == f y [ B ↓ p ]} (r : apd f p == q)
  {u : C x (f x)} {v : C y (f y)}
  → u == v [ uncurry C ↓ pair= p q ]
  → u == v [ (λ z → C z (f z)) ↓ p ]
↓-apd-out C {p = idp} idp idp = idp

-- Dependent paths over [ap f p]
module _ {i j k} {A : Set i} {B : Set j} (C : B → Set k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ ap f p ]
  ↓-ap-in {p = idp} idp = idp

  ↓-ap-out : {x y : A} (p : x == y) {u : C (f x)} {v : C (f y)}
    → u == v [ C ↓ ap f p ]
    → u == v [ C ∘ f ↓ p ]
  ↓-ap-out idp idp = idp

-- Mediating dependent paths with the transport version

module _ {i j} {A : Set i} where

  from-transp : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (transport B p u == v)
    → (u == v [ B ↓ p ])
  from-transp B idp idp = idp

  to-transp : {B : A → Set j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (transport B p u == v)
  to-transp {p = idp} idp = idp

  to-transp-β : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : transport B p u == v)
    → to-transp (from-transp B p q) == q
  to-transp-β B idp idp = idp

  to-transp-η : {B : A → Set j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp B p (to-transp q) == q
  to-transp-η {p = idp} idp = idp

  to-transp-equiv : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (transport B p u == v)
  to-transp-equiv B p =
    equiv to-transp (from-transp B p) (to-transp-β B p) (to-transp-η)


  from-transp! : (B : A → Set j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (u == transport! B p v)
    → (u == v [ B ↓ p ])
  from-transp! B idp idp = idp

  to-transp! : {B : A → Set j}
    {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (u == transport! B p v)
  to-transp! {p = idp} idp = idp

  to-transp!-β : (B : A → Set j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : u == transport! B p v)
    → to-transp! (from-transp! B p q) == q
  to-transp!-β B idp idp = idp

-- No idea what that is
to-transp-weird : ∀ {i j} {A : Set i} {B : A → Set j}
  {u v : A} {d : B u} {d' d'' : B v} {p : u == v}
  (q : d == d' [ B ↓ p ]) (r : transport B p d == d'')
  → (from-transp B p r ∙'dep (! r ∙ to-transp q)) == q
to-transp-weird {p = idp} idp idp = idp

-- Paths in the fibrations [fst] and [snd]
module _ {i j} where

  ↓-snd-in : {A A' : Type i} {B B' : Type j} (p : A == A') (q : B == B')
    {u : B} {v : B'}
    → u == v [ (λ X → X) ↓ q ]
    → u == v [ snd ↓ pair=' p q ]
  ↓-snd-in idp idp h = h

  ↓-fst-out : {A A' : Type i} {B B' : Type j} (p : A == A') (q : B == B')
    {u : A} {v : A'}
    → u == v [ fst ↓ pair=' p q ]
    → u == v [ (λ X → X) ↓ p ]
  ↓-fst-out idp idp h = h

-- Something not really clear yet
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → C) (g : B → C)
  where

  ↓-swap : {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
    (r : f a == g b') (s : f a' == g b)
    → (ap f p ∙' s == r [ (λ x → f a == g x)  ↓ q ])
    → (r == s ∙ ap g q  [ (λ x → f x == g b') ↓ p ])
  ↓-swap {p = idp} {q = idp} r s t = (! t) ∙ ∙'-unit-l s ∙ ! (∙-unit-r s)

  ↓-swap! : {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
    (r : f a == g b') (s : f a' == g b)
    → (r == s ∙ ap g q  [ (λ x → f x == g b') ↓ p ])
    → (ap f p ∙' s == r [ (λ x → f a == g x)  ↓ q ])
  ↓-swap! {p = idp} {q = idp} r s t = ∙'-unit-l s ∙ ! (∙-unit-r s) ∙ (! t)

