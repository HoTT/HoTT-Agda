{-# OPTIONS --without-K #-}

open import lib.Base

module lib.PathGroupoid {i} {A : Type i} where

-- infixr 8 _∙_

-- _∙_ : {x y z : A}
--   → (x == y → y == z → x == z)
-- q ∙ idp = q

-- Composition with the opposite definitional behaviour
_∙'_ : {x y z : A}
  → (x == y → y == z → x == z)
idp ∙' q = q

-- ! : {x y : A}
--   → (x == y → y == x)
-- ! idp = idp

∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
  → (p ∙ q) ∙ r == p ∙ (q ∙ r)
∙-assoc _ _ idp = idp

-- [∙-unit-r] and [∙'-unit-l] are definitional

∙-unit-l : {x y : A} (q : x == y) → idp ∙ q == q
∙-unit-l idp = idp

∙'-unit-r : {x y : A} (q : x == y) → q ∙' idp == q
∙'-unit-r idp = idp

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
