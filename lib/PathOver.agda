{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Funext
open import lib.Equivalences
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

--  ↓-ap-β
{-
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

-- These lemmas do not really look computational, but they are only used in the
-- [↓-pp] lemmas which do look computational.

module _ {i j} {A : Set i} where

  from-transp : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (coe (ap B p) u == v)
    → (u == v [ B ↓ p ])
  from-transp B idp idp = idp

  to-transp : {B : A → Set j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (coe (ap B p) u == v)
  to-transp {p = idp} idp = idp

  to-transp-β : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : coe (ap B p) u == v)
    → to-transp (from-transp B p q) == q
  to-transp-β B idp idp = idp

  to-transp-η : {B : A → Set j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp B p (to-transp q) == q
  to-transp-η {p = idp} idp = idp

  to-transp-equiv : (B : A → Set j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (coe (ap B p) u == v)
  to-transp-equiv B p =
    equiv to-transp (from-transp B p) (to-transp-β B p) (to-transp-η)

from-transp! : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  → (u == coe! (ap B p) v)
  → (u == v [ B ↓ p ])
from-transp! B idp idp = idp

to-transp! : ∀ {i j} {A : Set i} {B : A → Set j}
  {a a' : A} {p : a == a'}
  {u : B a} {v : B a'}
  → (u == v [ B ↓ p ])
  → (u == coe! (ap B p) v)
to-transp! {p = idp} idp = idp

to-transp!-β : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  (q : u == coe! (ap B p) v)
  → to-transp! (from-transp! B p q) == q
to-transp!-β B idp idp = idp


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
  → (from-transp B p r ∙'dep (! r ∙ to-transp q)) == q
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
