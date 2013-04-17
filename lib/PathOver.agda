{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Sigma
open import lib.PathGroupoid
open import lib.Funext
open import lib.Univalence

module lib.PathOver where

apdd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → g u == g v [ uncurry C ↓ pair= p q ]
apdd g p q = apd (uncurryi g) (pair= p q)

-- Dependent paths in a constant fibration
module _ {i j} {A : Set i} {B : Set j} where

  ↓-cst-in : {x y : A} (p : x == y) {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in idp q = q

  ↓-cst-out : {x y : A} {p : x == y} {u v : B}
    → u == v [ (λ _ → B) ↓ p ]
    → u == v
  ↓-cst-out {p = idp} q = q

  ↓-cst-β : {x y : A} (p : x == y) {u v : B} (q : u == v)
    → (↓-cst-out (↓-cst-in p q) == q)
  ↓-cst-β idp q = idp

-- Dependent paths in a constant fibration XX
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

-- Dependent paths in a constant fibration XX
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

-- Dependent paths in a Π-type
module _ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k} where

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
module _ {i j k} {A : Set i} {B : A → Set j} {C : Set k} {x x' : A} {p : x == x'}
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
module _ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
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
module _ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k}
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

split-ap2 : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} (f : Σ A B → C)
  {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → ap f (pair= p q) == ↓-app→cst-out (apd (curry f) p) q
split-ap2 f idp idp = idp

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

{- Not used yet

apdd-cst : ∀ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k}
  (g : (a : A) → Π B (C a)) {x y : A} (p : x ≡ y)
  {u v : B} (q : u ≡ v) {r : u ≡[ (λ _ → B) ↓ p ] v} (α : ↓-cst-in p q ≡ r)
  → apdd (λ {a} b → g a b) p r ≡ apd (uncurry g) (pair= p r)
apdd-cst g idp idp idp = idp
-}
-- This one seems a bit weird
↓-apd-out : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k)
  (f : Π A B) {x y : A} (p : x == y)
  {u : C x (f x)} {v : C y (f y)}
  → u == v [ uncurry C ↓ pair= p (apd f p) ]
  → u == v [ (λ z → C z (f z)) ↓ p ]
↓-apd-out C f idp idp = idp
{-
-- Dependent paths over [ap f p]
module _ {i j k} {A : Set i} {B : Set j} (C : B → Set k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x ≡ y} {u : C (f x)} {v : C (f y)}
    → u ≡[ C ◯ f ↓ p ] v
    → u ≡[ C ↓ ap f p ] v
  ↓-ap-in {p = idp} idp = idp

  ↓-ap-out : {x y : A} (p : x ≡ y) {u : C (f x)} {v : C (f y)}
    → u ≡[ C ↓ ap f p ] v
    → u ≡[ C ◯ f ↓ p ] v
  ↓-ap-out idp idp = idp

--  ↓-ap-β

ap-, : ∀ {i j k} {A : Set i} {B : Set j} {C : B → Set k}
  (f : A → B) (g : (a : A) → C (f a)) {x y : A} (p : x ≡ y)
  → ap (λ x → _,_ {P = C} (f x) (g x)) p
       ≡ pair= (ap f p) (↓-ap-in C f (apd g p))
ap-, f g idp = idp
-}

-- Special case of [ap-,]
ap-cst,id : ∀ {i j} {A : Set i} (B : A → Set j)
  {a : A} {x y : B a} (p : x == y)
  → ap (λ x → _,_ {B = B} a x) p == pair= idp p
ap-cst,id B idp = idp

-- apd-nd : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
--   → (p : x ≡ y) → apd f p ≡ ↓-cst-in p (ap f p)
-- apd-nd f idp = idp

apd-∘ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (f : Π A B) (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x == y)
  → apd (g ∘ f) p == ↓-apd-out C f p (apdd g p (apd f p))
apd-∘ f g idp = idp

{- Not used yet

-- apd-apd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
--   (g : (u : Σ A B) → C (π₁ u) (π₂ u)) (f : Π A B) {x y : A} (p : x ≡ y)
--   → apd g (pair= p (apd f p)) ≡ {!↓-ap-in!}
-- apd-apd = {!!}


apd-π₁-β : ∀ {i j} {A : Set i} {B : A → Set j} {x x' : A} (p : x ≡ x')
  {y : B x} {y' : B x'} (q : y ≡[ B ↓ p ] y')
  → ap π₁ (pair= p q) ≡ p
apd-π₁-β idp idp = idp

apd-π₂-β : ∀ {i j} {A : Set i} {B : A → Set j} {x x' : A} (p : x ≡ x')
  {y : B x} {y' : B x'} (q : y ≡[ B ↓ p ] y')
  → apd π₂ (pair= p q) ≡ ↓-ap-out B π₁ (pair= p q)
    (transport (λ p → y ≡[ B ↓ p ] y') (! (apd-π₁-β p q)) q)
apd-π₂-β idp idp = idp
-}

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

-- These lemmas do not really look computational, but they are only used in the
-- [↓-pp] lemmas which do look computational.

to-transp-in : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  → (coe (ap B p) u == v)
  → (u == v [ B ↓ p ])
to-transp-in B idp idp = idp

to-transp-out : ∀ {i j} {A : Set i} {B : A → Set j}
  {a a' : A} {p : a == a'}
  {u : B a} {v : B a'}
  → (u == v [ B ↓ p ])
  → (coe (ap B p) u == v)
to-transp-out {p = idp} idp = idp

to-transp-β : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  (q : coe (ap B p) u == v)
  → to-transp-out (to-transp-in B p q) == q
to-transp-β B idp idp = idp


-- Stuff that do not belong here

ap-∙' : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
  {x y z : A} (p : x == y) (q : y == z)
  → ap f (p ∙' q) == (ap f p ∙' ap f q)
ap-∙' f idp idp = idp

-- Dependent concatenation'
_∙'dep_ : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  → (u == v [ B ↓ p ]
   → v == w [ B ↓ p' ]
   → u == w [ B ↓ (p ∙' p') ])
_∙'dep_ {p' = idp} q idp = q

-- Dependent concatenation'
_∙dep_ : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  → (u == v [ B ↓ p ]
   → v == w [ B ↓ p' ]
   → u == w [ B ↓ (p ∙ p') ])
_∙dep_ {p = idp} idp q = q

-- Implementation of [_∙'_] on Σ
Σ-∙' : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
  → (pair= p q ∙' pair= p' r) == pair= (p ∙' p') (q ∙'dep r)
Σ-∙' {p' = idp} q idp = idp

-- Implementation of [_∙_] on Σ
Σ-∙ : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
  → (pair= p q ∙ pair= p' r) == pair= (p ∙ p') (q ∙dep r)
Σ-∙ {p = idp} idp q = idp

-- No idea what that is
to-transp-weird : ∀ {i j} {A : Set i} {B : A → Set j}
  {u v : A} {d : B u} {d' d'' : B v} {p : u == v}
  (q : d == d' [ B ↓ p ]) (r : coe (ap B p) d == d'')
  → (to-transp-in B p r ∙'dep (! r ∙ to-transp-out q)) == q
to-transp-weird {p = idp} idp idp = idp


_∙'2_ : ∀ {i j} {A : Set i} {B : A → Set j} {a b c : Π A B}
  {x y : A} {p : x == y} {q : a x == b x} {q' : a y == b y}
  {r : b x == c x} {r' : b y == c y}
  → (q == q'            [ (λ z → a z == b z) ↓ p ])
  → (r == r'            [ (λ z → b z == c z) ↓ p ])
  → (q ∙' r == q' ∙' r' [ (λ z → a z == c z) ↓ p ])
_∙'2_ {p = idp} idp idp = idp

stuff : ∀ {i j} {A : Set i} {B : Set j} {b : B} {c : A → B} {d : A → B}
  (q : (a : A) → b == c a) (r : (a : A) → c a == d a) {a a' : A} (p : a == a')
  → apd (λ a → q a ∙' r a) p == ((apd q p) ∙'2 (apd r p))
stuff q r idp = idp


apd= : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B} (q : (x : A) → f x == g x) {x y : A} (p : x == y)
--    → (q x == q y [ (λ z → f z == g z) ↓ p ])
  → (apd f p ▹ q y) == (q x ◃ apd g p)
apd= q p = ! (↓-=-out (apd q p))
--apd= q idp = 
