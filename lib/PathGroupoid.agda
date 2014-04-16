{-# OPTIONS --without-K #-}

open import lib.Base

module lib.PathGroupoid where

module _ {i} {A : Type i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 8 _∙_ _∙'_

  _∙_ : {x y z : A}
    → (x == y → y == z → x == z)
  idp ∙ q = q

  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  ∙=∙' : {x y z : A} (p : x == y) (q : y == z)
    → p ∙ q == p ∙' q
  ∙=∙' idp idp = idp

  ∙'=∙ : {x y z : A} (p : x == y) (q : y == z)
    → p ∙' q == p ∙ q
  ∙'=∙ idp idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp idp idp = idp

  -- [∙-unit-l] and [∙'-unit-r] are definitional

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  ∙'-unit-l : {x y : A} (q : x == y) → idp ∙' q == q
  ∙'-unit-l idp = idp

  {- Reversal of paths -}

  ! : {x y : A} → (x == y → y == x)
  ! idp = idp

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

  {- Interactions between operations

  A lemma of the form [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  and so on.
  -}

  !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  !-∙ idp idp = idp

  ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  ∙-! idp idp = idp

  !-! : {x y : A} (p : x == y) → ! (! p) == p
  !-! idp = idp

  {- Horizontal compositions -}

  _∙2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _∙2_ {p = idp} idp β = β

  _∙'2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙' q == p' ∙' q'
  _∙'2_ {q = idp} α idp = α

  idp∙2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙2 (idp {a = q}) == idp
  idp∙2idp idp idp = idp

  idp∙'2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙'2 (idp {a = q}) == idp
  idp∙'2idp idp idp = idp

{-
Sometimes we need to restart a new section in order to have everything in the
previous one generalized.
-}
module _ {i} {A : Type i} where
  {- Whisker and horizontal composition for Eckmann-Hilton argument -}
  _∙ᵣ_ : {x y z : A} {p p' : x == y} (α : p == p') (q : y == z)
    → p ∙ q == p' ∙ q
  _∙ᵣ_ {p = p} {p' = p'} α idp = ∙-unit-r p ∙ α ∙ ! (∙-unit-r p')

  _∙ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
    → p ∙ q == p ∙ q'
  _∙ₗ_ {q = q} {q' = q'} idp β = β

  _⋆2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
         (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆2_ {p' = p'} {q = q} α β = (α ∙ᵣ q) ∙ (p' ∙ₗ β)

  _⋆'2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
          (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆'2_ {p = p} {q' = q'} α β = (p ∙ₗ β) ∙ (α ∙ᵣ q')

  ⋆2=⋆'2 : {x y z : A} {p p' : x == y} {q q' : y == z}
           (α : p == p') (β : q == q')
    → α ⋆2 β == α ⋆'2 β
  ⋆2=⋆'2 {p = idp} {q = idp} idp idp = idp

module _ {i} {A : Type i} where

  -- Useful ?
  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

  -- anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
  --   → (p ∙ q == p ∙ r → q == r)
  -- anti-whisker-left idp h = h


{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} where

  {- Dependent constant path -}

  idpᵈ : {x : A} {u : B x} → u == u [ B ↓ idp ]
  idpᵈ = idp

  {- Dependent opposite path -}

  !ᵈ : {x y : A} {p : x == y} {u : B x} {v : B y}
    → (u == v [ B ↓ p ] → v == u [ B ↓ (! p)])
  !ᵈ {p = idp} = !

  {- Dependent concatenation -}

  _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙ᵈ_ {p = idp} {p' = idp} q r = q ∙ r

  _◃_ = _∙ᵈ_

  ◃idp : {x : A} {v w : B x} (q : w == v)
    → q ◃ idp == q
  ◃idp idp = idp

  _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙' p') ])
  _∙'ᵈ_ {p = idp} {p' = idp} q r = q ∙' r

  _▹_ = _∙'ᵈ_

  {- That’s not perfect, because [q] could be a dependent path. But in that case
     this is not well typed… -}
  idp▹ : {x : A} {v w : B x} (q : v == w)
    → idp ▹ q == q
  idp▹ idp = idp

  ▹idp : {x y : A} {p : x == y}
    {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → q ▹ idp == q
  ▹idp {p = idp} idp = idp

  _▹!_ : {x y z : A} {p : x == y} {p' : z == y}
    {u : B x} {v : B y} {w : B z}
    → u == v [ B ↓ p ]
    → w == v [ B ↓ p' ]
    → u == w [ B ↓ p ∙' (! p') ]
  _▹!_ {p' = idp} q idp = q

  idp▹! : {x : A} {v w : B x} (q : w == v)
    → idp ▹! q == ! q
  idp▹! idp = idp

  _!◃_ : {x y z : A} {p : y == x} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → v == u [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (! p) ∙ p' ]
  _!◃_ {p = idp} idp q = q

  !◃idp :{x : A} {v w : B x} (q : v == w)
    → q !◃ idp == ! q
  !◃idp idp = idp


  {-
  This is some kind of dependent horizontal composition (used in [apd∙]).
  -}

  _∙2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙ r == q' ∙ r' [ (λ a → x a == z a) ↓ p ])
  _∙2ᵈ_ {p = idp} α β = α ∙2 β

  _∙'2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙' r == q' ∙' r' [ (λ a → x a == z a) ↓ p ])
  _∙'2ᵈ_ {p = idp} α β = α ∙'2 β

  {-
  [apd∙] reduces a term of the form [apd (λ a → q a ∙ r a) p], do not confuse it
  with [apd-∙] which reduces a term of the form [apd f (p ∙ q)].
  -}

  apd∙ : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙ r a) p == apd q p ∙2ᵈ apd r p
  apd∙ q r idp = ! (idp∙2idp (q _) (r _))

  apd∙' : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙' r a) p == apd q p ∙'2ᵈ apd r p
  apd∙' q r idp = ! (idp∙'2idp (q _) (r _))

module _ {i j} {A : Type i} {B : A → Type j} where

  {- Exchange -}

  ▹-∙'2ᵈ : {x y z : Π A B}
    {a a' a'' : A} {p : a == a'} {p' : a' == a''}
    {q0 : x a == y a} {q0' : x a' == y a'}
    {r0 : y a == z a} {r0' : y a' == z a'}
    {q0'' : x a'' == y a''} {r0'' : y a'' == z a''}
    (q : q0 == q0' [ (λ a → x a == y a) ↓ p ])
    (r : r0 == r0' [ (λ a → y a == z a) ↓ p ])
    (s : q0' == q0'' [ (λ a → x a == y a) ↓ p' ])
    (t : r0' == r0'' [ (λ a → y a == z a) ↓ p' ])
    → (q ∙'2ᵈ r) ▹ (s ∙'2ᵈ t) == (q ▹ s) ∙'2ᵈ (r ▹ t)
  ▹-∙'2ᵈ {p = idp} {p' = idp} {q0} {.q0} {r0} {.r0} idp idp idp idp =
    ap (λ u → (idp {a = q0} ∙'2 idp {a = r0}) ∙' u) (idp∙'2idp q0 r0)
