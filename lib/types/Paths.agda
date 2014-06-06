{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Paths where

{- ! is an equivalence -}
module _ {i} {A : Type i} {x y : A} where

  !-equiv : (x == y) ≃ (y == x)
  !-equiv = equiv ! ! !-! !-!

{- Pre- and post- concatenation are equivalences -}
module _ {i} {A : Type i} {x y z : A} where

  pre∙-is-equiv : (p : x == y) → is-equiv (λ (q : y == z) → p ∙ q)
  pre∙-is-equiv p = is-eq (λ q → p ∙ q) (λ r → ! p ∙ r) f-g g-f
    where f-g : ∀ r → p ∙ ! p ∙ r == r
          f-g r = ! (∙-assoc p (! p) r) ∙ ap (λ s → s ∙ r) (!-inv-r p)

          g-f : ∀ q → ! p ∙ p ∙ q == q
          g-f q = ! (∙-assoc (! p) p q) ∙ ap (λ s → s ∙ q) (!-inv-l p)

  pre∙-equiv : (p : x == y) → (y == z) ≃ (x == z)
  pre∙-equiv p = ((λ q → p ∙ q) , pre∙-is-equiv p)

  post∙-is-equiv : (p : y == z) → is-equiv (λ (q : x == y) → q ∙ p)
  post∙-is-equiv p = is-eq (λ q → q ∙ p) (λ r → r ∙ ! p) f-g g-f
    where f-g : ∀ r → (r ∙ ! p) ∙ p == r
          f-g r = ∙-assoc r (! p) p ∙ ap (λ s → r ∙ s) (!-inv-l p) ∙ ∙-unit-r r

          g-f : ∀ q → (q ∙ p) ∙ ! p == q
          g-f q = ∙-assoc q p (! p) ∙ ap (λ s → q ∙ s) (!-inv-r p) ∙ ∙-unit-r q

  post∙-equiv : (p : y == z) → (x == y) ≃ (x == z)
  post∙-equiv p = ((λ q → q ∙ p) , post∙-is-equiv p)

module _ {i j} {A : Type i} {B : Type j} {f : A → B} {b : B} where

  ↓-app=cst-in : {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙ v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-in {p = idp} q = q

  ↓-app=cst-out : {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙ v)
  ↓-app=cst-out {p = idp} r = r

  ↓-app=cst-eqv : {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
    → (u == (ap f p ∙ v)) ≃ (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-eqv {p = idp} = equiv ↓-app=cst-in ↓-app=cst-out 
                             
     (λ _ → idp) (λ _ → idp)

  ↓-cst=app-in : {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙' ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-in {p = idp} idp = idp

  ↓-cst=app-out : {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙' ap f p) == v
  ↓-cst=app-out {p = idp} idp = idp

module _ {i} {A : Type i} where

  ↓-app=idf-in : {f : A → A} {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u ∙' p == ap f p ∙ v
    → u == v [ (λ z → f z == z) ↓ p ]
  ↓-app=idf-in {p = idp} q = q

  ↓-cst=idf-in : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙ p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in {p = idp} q = ! (∙-unit-r _) ∙ q

  {- I'm not sure about the naming, but I think this is actually
   - more compatible with [↓-app=idf-in].
   -}
  ↓-cst=idf-in' : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙' p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in' {p = idp} q = q

  ↓-idf=cst-in : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → u == p ∙' v
    → (u == v [ (λ x → x == a) ↓ p ])
  ↓-idf=cst-in {p = idp} q = q ∙ ∙'-unit-l _

  ↓-idf=idf-in : {x y : A} {p : x == y} {u : x == x} {v : y == y}
    → u ∙ p == p ∙' v
    → (u == v [ (λ x → x == x) ↓ p ])
  ↓-idf=idf-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ ∙'-unit-l _

{- Nondependent identity type -}

↓-='-in : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → (u ∙ ap g p) == (ap f p ∙' v)
  → (u == v [ (λ x → f x == g x) ↓ p ])
↓-='-in {p = idp} q = ! (∙-unit-r _) ∙ q ∙ (∙'-unit-l _)

↓-='-out : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → (u == v [ (λ x → f x == g x) ↓ p ])
  → (u ∙ ap g p) == (ap f p ∙' v)
↓-='-out {p = idp} q = (∙-unit-r _) ∙ q ∙ ! (∙'-unit-l _)

{- Identity type where the type is dependent -}

↓-=-in : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u ◃ apd f p) == (apd g p ▹ v)
  → (u == v [ (λ x → g x == f x) ↓ p ])
↓-=-in {B = B} {p = idp} {u} {v} q = ! (◃idp {B = B} u) ∙ q ∙ idp▹ {B = B} v

↓-=-out : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u == v [ (λ x → g x == f x) ↓ p ])
  → (u ◃ apd f p) == (apd g p ▹ v)
↓-=-out {B = B} {p = idp} {u} {v} q = (◃idp {B = B} u) ∙ q ∙ ! (idp▹ {B = B} v)

-- Dependent path in a type of the form [λ x → g (f x) ≡ x]
module _ {i j} {A : Type i} {B : Type j} (g : B → A) (f : A → B) where
  ↓-∘=idf-in : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → ((ap g (ap f p) ∙' v) == (u ∙ p))
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-∘=idf-in {p = idp} q = ! (∙-unit-r _) ∙ (! q) ∙ (∙'-unit-l _)

-- WIP, derive it from more primitive principles
-- ↓-∘≡id-in f g {p = p} {u} {v} q =
--   ↓-≡-in (u ◃ apd (λ x → g (f x)) p =⟨ apd-∘ f g p |in-ctx (λ t → u ◃ t) ⟩
--         u ◃ ↓-apd-out _ f p (apdd g p (apd f p)) =⟨ apdd-cst (λ _ b → g b) p (ap f p) (! (apd-nd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (apd (λ t → g (π₂ t)) (pair= p (apd f p))) =⟨ apd-∘ π₂ g (pair= p (apd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (↓-apd-out _ π₂ (pair= p (apd f p)) (apdd g (pair= p (apd f p)) (apd π₂ (pair= p (apd f p))))) =⟨ {!!} ⟩
--         apd (λ x → x) p ▹ v ∎)

-- module _ {i j} {A : Type i} {B : Type j} {x y z : A → B} where

--   lhs : 
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     (α : q == q'            [ (λ a → x a == y a) ↓ p ])
--     (β : r ∙ ap z p == ap y p ∙' r')
--     → (q ∙' r) ∙ ap z p == ap x p ∙' q' ∙' r'
--   lhs =
--     (q ∙' r) ∙ ap z p     =⟨ ? ⟩  -- assoc
--     q ∙' (r ∙ ap z p)     =⟨ ? ⟩  -- β
--     q ∙' (ap y p ∙' r')   =⟨ ? ⟩  -- assoc
--     (q ∙' ap y p) ∙' r'   =⟨ ? ⟩  -- ∙ = ∙'
--     (q ∙ ap y p) ∙' r'    =⟨ ? ⟩  -- α
--     (ap x p ∙' q') ∙' r'  =⟨ ? ⟩  -- assoc
--     ap x p ∙' q' ∙' r' ∎
    

--   thing :
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     (α : q == q'            [ (λ a → x a == y a) ↓ p ])
--     (β : r ∙ ap z p == ap y p ∙' r')
--     → (_∙'2ᵈ_ {r = r} {r' = r'} α (↓-='-in β) == ↓-='-in {!!})
--   thing = {!!}
