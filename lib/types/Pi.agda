{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Pi where

-- Dependent paths in a Π-type
module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} where

  ↓-Π-in : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ pair= p q ])
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
  ↓-Π-in {p = idp} f = funext (λ x → f (idp {a = x}))

  ↓-Π-out : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ pair= p q ])
  ↓-Π-out {p = idp} q idp = happly q _

  ↓-Π-β : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (f : {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
            → u t == u' t' [ uncurry C ↓ pair= p q ])
    → {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
    → ↓-Π-out (↓-Π-in f) q == f q
  ↓-Π-β {p = idp} f idp = happly (happly-funext (λ x → f (idp {a = x}))) _

-- Dependent paths in a Π-type where the codomain is not dependent on anything
module _ {i j k} {A : Type i} {B : A → Type j} {C : Type k} {x x' : A} {p : x == x'}
  {u : B x → C} {u' : B x' → C} where

  ↓-app→cst-in :
    ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
      → u t == u' t')
    → (u == u' [ (λ x → B x → C) ↓ p ])
  ↓-app→cst-in f = ↓-Π-in (λ q → ↓-cst-in (pair= p q) (f q))

  ↓-app→cst-out :
    (u == u' [ (λ x → B x → C) ↓ p ])
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t')
  ↓-app→cst-out r q = ↓-cst-out (↓-Π-out r q)

  ↓-app→cst-β :
    (f : ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
           → u t == u' t'))
    → {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
    → ↓-app→cst-out (↓-app→cst-in f) q == f q
  ↓-app→cst-β f q =
    ↓-app→cst-out (↓-app→cst-in f) q
             =⟨ idp ⟩
    ↓-cst-out (↓-Π-out (↓-Π-in (λ qq → ↓-cst-in (pair= p qq) (f qq))) q)
             =⟨ ↓-Π-β (λ qq → ↓-cst-in (pair= p qq) (f qq)) q |in-ctx ↓-cst-out ⟩
    ↓-cst-out (↓-cst-in (pair= p q) (f q))
             =⟨ ↓-cst-β (pair= p q) (f q) ⟩
    f q ∎

-- Dependent paths in an arrow type
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  {x x' : A} {p : x == x'} {u : B x → C x} {u' : B x' → C x'} where

  ↓-→-in :
    ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
      → u t == u' t' [ C ↓ p ])
    → (u == u' [ (λ x → B x → C x) ↓ p ])
  ↓-→-in f = ↓-Π-in (λ q → ↓-cst2-in p q (f q))

  ↓-→-out :
    (u == u' [ (λ x → B x → C x) ↓ p ])
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
      → u t == u' t' [ C ↓ p ])
  ↓-→-out r q = ↓-cst2-out p q (↓-Π-out r q)

  -- ↓-app→cst-out :
  --   (u == u' [ (λ x → B x → C) ↓ p ])
  --   → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
  --       → u t == u' t')
  -- ↓-app→cst-out r q = ↓-cst-out (↓-Π-out r q)

  -- ↓-app→cst-β :
  --   (f : ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
  --          → u t == u' t'))
  --   → {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
  --   → ↓-app→cst-out (↓-app→cst-in f) q == f q
  -- ↓-app→cst-β f q =
  --   ↓-app→cst-out (↓-app→cst-in f) q
  --            =⟨ idp ⟩
  --   ↓-cst-out (↓-Π-out (↓-Π-in (λ qq → ↓-cst-in (pair= p qq) (f qq))) q)
  --            =⟨ ↓-Π-β (λ qq → ↓-cst-in (pair= p qq) (f qq)) q |in-ctx ↓-cst-out ⟩
  --   ↓-cst-out (↓-cst-in (pair= p q) (f q))
  --            =⟨ ↓-cst-β (pair= p q) (f q) ⟩
  --   f q ∎

-- Dependent paths in a Π-type where the domain is constant
module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k}
  {x x' : A} {p : x == x'}
  {u : (b : B) → C x b} {u' : (b : B) → C x' b} where

  postulate
    ↓-cst→app-in :
      ({t t' : B} (q : t == t')
        → u t == u' t' [ uncurry C ↓ pair= p (↓-cst-in p q) ])
      → (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
--  ↓-cst→app-in f = ↓-Π-in (λ q → {!f (↓-cst-out q)!})

  postulate
    ↓-cst→app-out :
      (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
      → ({t t' : B} (q : t == t')
        → u t == u' t' [ uncurry C ↓ pair= p (↓-cst-in p q) ])

split-ap2 : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k} (f : Σ A B → C)
  {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → ap f (pair= p q) == ↓-app→cst-out (apd (curry f) p) q
split-ap2 f idp idp = idp
