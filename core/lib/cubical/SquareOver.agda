{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathOver
open import lib.cubical.Square

module lib.cubical.SquareOver where

SquareOver : ∀ {i j} {A : Type i} (B : A → Type j) {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  (q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]) (q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ])
  (q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]) (q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ])
  → Type j
SquareOver B ids = Square

apd-square : ∀ {i j} {A : Type i} {B : A → Type j} (f : Π A B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (sq : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → SquareOver B sq (apd f p₀₋) (apd f p₋₀) (apd f p₋₁) (apd f p₁₋)
apd-square f ids = ids

↓-=-to-squareover : ∀ {i j} {A : Type i} {B : A → Type j}
  {f g : Π A B} {x y : A} {p : x == y}
  {u : f x == g x} {v : f y == g y}
  → u == v [ (λ z → f z == g z) ↓ p ]
  → SquareOver B vid-square u (apd f p) (apd g p) v
↓-=-to-squareover {p = idp} idp = hid-square

↓-=-from-squareover : ∀ {i j} {A : Type i} {B : A → Type j}
  {f g : Π A B} {x y : A} {p : x == y}
  {u : f x == g x} {v : f y == g y}
  → SquareOver B vid-square u (apd f p) (apd g p) v
  → u == v [ (λ z → f z == g z) ↓ p ]
↓-=-from-squareover {p = idp} sq = horiz-degen-path sq

squareover-cst-in : ∀ {i j} {A : Type i} {B : Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq : Square p₀₋ p₋₀ p₋₁ p₁₋}
  {b₀₀ b₀₁ b₁₀ b₁₁ : B}
  {q₀₋ : b₀₀ == b₀₁} {q₋₀ : b₀₀ == b₁₀} {q₋₁ : b₀₁ == b₁₁} {q₁₋ : b₁₀ == b₁₁}
  (sq' : Square q₀₋ q₋₀ q₋₁ q₁₋)
  → SquareOver (λ _ → B) sq
      (↓-cst-in q₀₋) (↓-cst-in q₋₀) (↓-cst-in q₋₁) (↓-cst-in q₁₋)
squareover-cst-in {sq = ids} sq' = sq'

↓↓-from-squareover : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k}
  {x y : C → A} {u : (c : C) → B (x c)} {v : (c : C) → B (y c)}
  {p : (c : C) → x c == y c} {c₁ c₂ : C} {q : c₁ == c₂}
  {α : u c₁ == v c₁ [ B ↓ p c₁ ]} {β : u c₂ == v c₂ [ B ↓ p c₂ ]}
  → SquareOver B (natural-square p q)
               α (↓-ap-in _ _ (apd u q)) (↓-ap-in _ _ (apd v q)) β
  → α == β [ (λ c → u c == v c [ B ↓ p c ]) ↓ q ]
↓↓-from-squareover {q = idp} sq = lemma sq
  where
  lemma : ∀ {i j} {A : Type i} {B : A → Type j}
    {x y : A} {u : B x} {v : B y} {p : x == y}
    {α β : u == v [ B ↓ p ]}
    → SquareOver B hid-square α idp idp β
    → α == β
  lemma {p = idp} sq = horiz-degen-path sq

↓↓-to-squareover : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k}
  {x y : C → A} {u : (c : C) → B (x c)} {v : (c : C) → B (y c)}
  {p : (c : C) → x c == y c} {c₁ c₂ : C} {q : c₁ == c₂}
  {α : u c₁ == v c₁ [ B ↓ p c₁ ]} {β : u c₂ == v c₂ [ B ↓ p c₂ ]}
  → α == β [ (λ c → u c == v c [ B ↓ p c ]) ↓ q ]
  → SquareOver B (natural-square p q)
               α (↓-ap-in _ _ (apd u q)) (↓-ap-in _ _ (apd v q)) β
↓↓-to-squareover {q = idp} r = lemma r
  where
  lemma : ∀ {i j} {A : Type i} {B : A → Type j}
    {x y : A} {u : B x} {v : B y} {p : x == y}
    {α β : u == v [ B ↓ p ]}
    → α == β
    → SquareOver B hid-square α idp idp β
  lemma {p = idp} r = horiz-degen-square r

infixr 80 _∙v↓⊡_ _∙h↓⊡_ _↓⊡v∙_ _↓⊡h∙_

_∙h↓⊡_ : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq : Square p₀₋ p₋₀ p₋₁ p₁₋}
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  {q₀₋ q₀₋' : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ]}
  {q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
  → q₀₋ == q₀₋'
  → SquareOver B sq q₀₋' q₋₀ q₋₁ q₁₋
  → SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋
_∙h↓⊡_ {sq = ids} = _∙h⊡_

_∙v↓⊡_ : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq : Square p₀₋ p₋₀ p₋₁ p₁₋}
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  {q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {q₋₀ q₋₀' : b₀₀ == b₁₀ [ B ↓ p₋₀ ]}
  {q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
  → q₋₀ == q₋₀'
  → SquareOver B sq q₀₋ q₋₀' q₋₁ q₁₋
  → SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋
_∙v↓⊡_ {sq = ids} = _∙v⊡_

_↓⊡v∙_ : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq : Square p₀₋ p₋₀ p₋₁ p₁₋}
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  {q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ]}
  {q₋₁ q₋₁' : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {q₁₋ : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
  → SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋
  → q₋₁ == q₋₁'
  → SquareOver B sq q₀₋ q₋₀ q₋₁' q₁₋
_↓⊡v∙_ {sq = ids} = _⊡v∙_

_↓⊡h∙_ : ∀ {i j} {A : Type i} {B : A → Type j} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  {sq : Square p₀₋ p₋₀ p₋₁ p₁₋}
  {b₀₀ : B a₀₀} {b₀₁ : B a₀₁} {b₁₀ : B a₁₀} {b₁₁ : B a₁₁}
  {q₀₋ : b₀₀ == b₀₁ [ B ↓ p₀₋ ]} {q₋₀ : b₀₀ == b₁₀ [ B ↓ p₋₀ ]}
  {q₋₁ : b₀₁ == b₁₁ [ B ↓ p₋₁ ]} {q₁₋ q₁₋' : b₁₀ == b₁₁ [ B ↓ p₁₋ ]}
  → SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋
  → q₁₋ == q₁₋'
  → SquareOver B sq q₀₋ q₋₀ q₋₁ q₁₋'
_↓⊡h∙_ {sq = ids} = _⊡h∙_
