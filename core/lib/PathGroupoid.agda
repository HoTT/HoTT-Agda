{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.PathGroupoid where

module _ {i} {A : Type i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 80 _∙_ _∙'_

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
  ∙-assoc idp _ _ = idp

  ∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙' q) ∙' r == p ∙' (q ∙' r)
  ∙'-assoc _ _ idp = idp

  ∙-∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙-∙'-assoc idp _ _ = idp

  ∙-∙'-assoc' : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙-∙'-assoc' _ _ idp = idp

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

  !-inv'-l : {x y : A} (p : x == y) → (! p) ∙' p == idp
  !-inv'-l idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

  !-inv'-r : {x y : A} (p : x == y) → p ∙' (! p) == idp
  !-inv'-r idp = idp

  {- Interactions between operations

  A lemma of the form [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  and so on.
  -}

  !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  !-∙ idp idp = idp

  ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  ∙-! idp idp = idp

  !-∙' : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙' q) == ! q ∙' ! p
  !-∙' idp idp = idp

  ∙'-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙' ! p == ! (p ∙' q)
  ∙'-! idp idp = idp

  !-! : {x y : A} (p : x == y) → ! (! p) == p
  !-! idp = idp

  {- Horizontal compositions -}

  infixr 80 _∙2_ _∙'2_

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

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-∙' : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙' q) == ap f p ∙' ap f q
  ap-∙' p idp = idp

{-
Sometimes we need to restart a new section in order to have everything in the
previous one generalized.
-}
module _ {i} {A : Type i} where
  {- Whisker and horizontal composition for Eckmann-Hilton argument -}

  infixr 80 _∙ᵣ_ _⋆2_ _⋆'2_
  infixl 80 _∙ₗ_

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

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

  anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
    → (p ∙ q == p ∙ r → q == r)
  anti-whisker-left idp h = h

  {-
  The order of the arguments p, q, r follows the occurrences
  of these variables in the output type
  -}

  post-rotate-in : {x y z : A} (p : x == y) (r : x == z) (q : y == z)
    → p ∙ q == r
    → p == r ∙ (! q)
  post-rotate-in p r idp e = ! (∙-unit-r p) ∙ e ∙ ! (∙-unit-r r)

  post-rotate-out : {x y z : A} (p : x == y) (q : y == z) (r : x == z)
    → p == r ∙ (! q)
    → p ∙ q == r
  post-rotate-out p idp r e = ∙-unit-r p ∙ e ∙ ∙-unit-r r

  post-rotate'-in : {x y z : A} (r : x == z) (q : y == z) (p : x == y)
    → r == p ∙ q
    → r ∙ (! q) == p
  post-rotate'-in r idp p e = ∙-unit-r r ∙ e ∙ ∙-unit-r p

  post-rotate'-out : {x y z : A} (r : x == z) (p : x == y) (q : y == z)
    → r ∙ (! q) == p
    → r == p ∙ q
  post-rotate'-out r p idp e = ! (∙-unit-r r) ∙ e ∙ ! (∙-unit-r p)

  pre-rotate-in : {x y z : A} (q : y == z) (p : x == y) (r : x == z)
    → p ∙ q == r
    → q == (! p) ∙ r
  pre-rotate-in q idp r e = e

  pre-rotate-out : {x y z : A} (p : x == y) (q : y == z) (r : x == z)
    → q == (! p) ∙ r
    → p ∙ q == r
  pre-rotate-out idp q r e = e

  pre-rotate'-in : {x y z : A} (p : x == y) (r : x == z) (q : y == z)
    → r == p ∙ q
    → (! p) ∙ r == q
  pre-rotate'-in idp r q e = e

  pre-rotate'-out : {x y z : A} (r : x == z) (p : x == y) (q : y == z)
    → (! p) ∙ r == q
    → r == p ∙ q
  pre-rotate'-out r idp q e = e


{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} where

  {- Dependent constant path -}

  idpᵈ : {x : A} {u : B x} → u == u [ B ↓ idp ]
  idpᵈ = idp

  {- Dependent opposite path -}

  !ᵈ : {x y : A} {p : x == y} {u : B x} {v : B y}
    → (u == v [ B ↓ p ] → v == u [ B ↓ (! p)])
  !ᵈ {p = idp} = !

  !ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (u == v [ B ↓ (! p) ] → v == u [ B ↓ p ])
  !ᵈ' {p = idp} = !

  !ᵈ-!ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (q : u == v [ B ↓ (! p) ])
    → !ᵈ (!ᵈ' q) == q
  !ᵈ-!ᵈ' {p = idp} idp = idp

  {- Dependent concatenation -}

  infixr 80 _∙ᵈ_ _∙'ᵈ_ _◃_ _▹_ _!◃_ _▹!_

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

  idp◃ : {x y : A} {p : x == y}
    {u : B x} {v : B y} (r : u == v [ B ↓ p ])
    → idp ◃ r == r
  idp◃ {p = idp} r = idp

  ∙ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} idp f₁₂ f₂₃ = idp

  infixr 80 _∙ᵈᵣ_
  infixl 80 _∙ᵈₗ_

  {- Dependent whiskering -}
  _∙ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → p ∙ᵈ q == p' ∙ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (λ r → r ∙ f) α ]
  _∙ᵈᵣ_ {α = idp} idp q = idp

  _∙ᵈₗ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {f : a₁ == a₂} {f' : a₁ == a₂}
    {α : f == f'}
    {q : b₁ == b₂ [ B ↓ f ]} {q' : b₁ == b₂ [ B ↓ f' ]}
    (p : b₀ == b₁ [ B ↓ e ])
    → (β : q == q' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → p ∙ᵈ q == p ∙ᵈ q' [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (λ r → e ∙ r) α ]
  _∙ᵈₗ_ {α = idp} q idp = idp

  _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙' p') ])
  _∙'ᵈ_ {p = idp} {p' = idp} q r = q ∙' r

  _▹_ = _∙'ᵈ_

  ∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙'ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙'ᵈ (f₁₂ ∙'ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} f₀₁ f₁₂ idp = idp

  ∙ᵈ-∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} idp f₁₂ f₂₃ = idp

  ∙ᵈ-∙'ᵈ-assoc' : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-∙'-assoc' e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc' {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} idp f₁₂ f₂₃ = idp

  _∙'ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → p ∙'ᵈ q == p' ∙'ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (λ r → r ∙' f) α ]
  _∙'ᵈᵣ_ {α = idp} idp q = idp

  {- That’s not perfect, because [q] could be a dependent path. But in that case
     this is not well typed… -}
  idp▹ : {x : A} {v w : B x} (q : v == w)
    → idp ▹ q == q
  idp▹ idp = idp

  ▹idp : {x y : A} {p : x == y}
    {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → q ▹ idp == q
  ▹idp {p = idp} idp = idp

  ◃▹-assoc : {a₀ a₁ a₂ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂}
    {b₀ : B a₀} {b₁ b₁' : B a₁} {b₂ : B a₂}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f' : b₁ == b₁') (f₁₂ : b₁' == b₂ [ B ↓ e₁₂ ])
    → (f₀₁ ▹ f') ∙ᵈ f₁₂ == f₀₁ ∙ᵈ (f' ◃ f₁₂)
  ◃▹-assoc {e₀₁ = idp} {e₁₂ = idp} f₀₁ idp f₁₂ = idp

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

  infixr 80 _∙2ᵈ_ _∙'2ᵈ_

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

  ∙ᵈᵣ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' e'' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]} {p'' : b₀ == b₁ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α' ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → (β ∙'ᵈ β') ∙ᵈᵣ q == (β ∙ᵈᵣ q) ∙'ᵈ (β' ∙ᵈᵣ q)
        [ (λ y → (p ∙ᵈ q) == (p'' ∙ᵈ q) [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (λ r → r ∙ f) α α' ]
  ∙ᵈᵣ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

  ∙ᵈₗ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {f : a₀ == a₁} {e e' e'' : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₁ == b₂ [ B ↓ e ]} {p' : b₁ == b₂ [ B ↓ e' ]} {p'' : b₁ == b₂ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α' ])
    → (q : b₀ == b₁ [ B ↓ f ])
    → q ∙ᵈₗ (β ∙'ᵈ β') == (q ∙ᵈₗ β) ∙'ᵈ (q ∙ᵈₗ β')
        [ (λ y → (q ∙ᵈ p) == (q ∙ᵈ p'') [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (λ r → f ∙ r) α α' ]
  ∙ᵈₗ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

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
