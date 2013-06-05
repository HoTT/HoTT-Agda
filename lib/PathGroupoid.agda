{-# OPTIONS --without-K #-}

open import lib.Base

module lib.PathGroupoid where

module _ {i} {A : Type i} where

  -- Composition with the opposite definitional behaviour
  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  ∙=∙' : {x y z : A} (p : x == y) (q : y == z)
    → p ∙ q == p ∙' q
  ∙=∙' idp idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp idp idp = idp

  -- [∙-unit-l] and [∙'-unit-r] are definitional

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  ∙'-unit-l : {x y : A} (q : x == y) → idp ∙' q == q
  ∙'-unit-l idp = idp

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

  -- -- Useful ?
  -- anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
  --   → (q ∙ p == r ∙ p → q == r)
  -- anti-whisker-right idp {q} {r} h =
  --   ! (idp-right-unit q) ∙ (h ∙ idp-right-unit r)

  -- anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
  --   → (p ∙ q == p ∙ r → q == r)
  -- anti-whisker-left idp h = h

  -- [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  -- and so on
  !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  !-∙ idp idp = idp

  ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  ∙-! idp idp = idp

  !-! : {x y : A} (p : x == y) → ! (! p) == p
  !-! idp = idp

-- Dependent things
module _ {i j} {A : Set i} {B : A → Set j} where

  -- Dependent concatenation'
  _∙dep_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙dep_ {p = idp} idp q = q

  -- Dependent concatenation'
  _∙'dep_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙' p') ])
  _∙'dep_ {p' = idp} q idp = q

  _∙'2_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙' r == q' ∙' r' [ (λ a → x a == z a) ↓ p ])
  _∙'2_ {p = idp} idp idp = idp

  _∙2_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙ r == q' ∙ r' [ (λ a → x a == z a) ↓ p ])
  _∙2_ {p = idp} idp idp = idp

  stuff : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙' r a) p == apd q p ∙'2 apd r p
  stuff q r idp = idp
