{-# OPTIONS --without-K #-}

-- Drop-in replacement for the module [Base].
module BaseOver where

-- We hide [apd] and [Σ-eq] because their type is not correct, we want to use
-- dependent paths instead
open import Base public hiding (apd; Σ-eq)

-- Notion of path over a path
path-over : ∀ {i j} {A : Set i} (B : A → Set j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set j
path-over B refl u v = (u == v)

syntax path-over B p u v =
  u == v [ B ↓ p ]

-- New apd
apd : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f refl = refl

-- Σ-types are used to simulate telescopes and to be able to only use the
-- notion of path over a single path

-- Intro for paths in a Σ
Σ-eq : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → (x , u) == (y , v)
Σ-eq refl refl = refl

uncurryi : ∀ {i j k} {A : Set i} {B : A → Set j} {C : ∀ x → B x → Set k}
  → (∀ {x} y → C x y) → (∀ s → C (π₁ s) (π₂ s))
uncurryi f (x , y) = f y

apdd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → g u == g v [ uncurry C ↓ Σ-eq p q ]
apdd g p q = apd (uncurryi g) (Σ-eq p q)

-- Dependent paths in a constant fibration
module _ {i j} {A : Set i} {B : Set j} where

  ↓-cst-in : {x y : A} (p : x == y) {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in refl q = q

  ↓-cst-out : {x y : A} {p : x == y} {u v : B}
    → u == v [ (λ _ → B) ↓ p ]
    → u == v
  ↓-cst-out {p = refl} q = q

  ↓-cst-β : {x y : A} (p : x == y) {u v : B} (q : u == v)
    → (↓-cst-out (↓-cst-in p q) == q)
  ↓-cst-β refl q = refl

-- -- ap can be defined via apd, not sure whether it’s a good idea or not
-- ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A} (p : x == y)
--   → f x == f y
-- ap f p = ↓-cst-out (apd f p)

-- Dependent paths in a Π-type
module _ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k} where

  ↓-Π-in : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ Σ-eq p q ])
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
  ↓-Π-in {p = refl} f = funext (λ x → f (refl {a = x}))

  ↓-Π-out : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ Σ-eq p q ])
  ↓-Π-out {p = refl} q refl = happly q _

  ↓-Π-β : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (f : {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
            → u t == u' t' [ uncurry C ↓ Σ-eq p q ])
    → {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
    → ↓-Π-out (↓-Π-in f) q == f q
  ↓-Π-β {p = refl} f refl = happly (happly-funext (λ x → f (refl {a = x}))) _

-- Dependent paths in a Π-type where the codomain is not dependent on anything
module _ {i j k} {A : Set i} {B : A → Set j} {C : Set k} {x x' : A} {p : x == x'}
  {u : B x → C} {u' : B x' → C} where

  ↓-app→cst-in :
    ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
      → u t == u' t')
    → (u == u' [ (λ x → B x → C) ↓ p ])
  ↓-app→cst-in f = ↓-Π-in (λ q → ↓-cst-in (Σ-eq p q) (f q))

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
             ≡⟨ refl ⟩
    ↓-cst-out (↓-Π-out (↓-Π-in (λ qq → ↓-cst-in (Σ-eq p qq) (f qq))) q)
             ≡⟨ ↓-Π-β (λ qq → ↓-cst-in (Σ-eq p qq) (f qq)) q |in-ctx ↓-cst-out ⟩
    ↓-cst-out (↓-cst-in (Σ-eq p q) (f q))
             ≡⟨ ↓-cst-β (Σ-eq p q) (f q) ⟩
    f q ∎

-- Dependent paths in a Π-type where the domain is constant
module _ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k}
  {x x' : A} {p : x == x'}
  {u : (b : B) → C x b} {u' : (b : B) → C x' b} where

  postulate
    ↓-cst→app-in :
      ({t t' : B} (q : t == t')
        → u t == u' t' [ uncurry C ↓ Σ-eq p (↓-cst-in p q) ])
      → (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
--  ↓-cst→app-in f = ↓-Π-in (λ q → {!f (↓-cst-out q)!})

  postulate
    ↓-cst→app-out :
      (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
      → ({t t' : B} (q : t == t')
        → u t == u' t' [ uncurry C ↓ Σ-eq p (↓-cst-in p q) ])

split-ap2 : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} (f : Σ A B → C)
  {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → ap f (Σ-eq p q) == ↓-app→cst-out (apd (curry f) p) q
split-ap2 f refl refl = refl

↓-app='cst-in : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
  → u == (ap f p ∘' v)
  → (u == v [ (λ x → f x == b) ↓ p ])
↓-app='cst-in {p = refl} q = q ∘ refl-left-unit _

↓-app='cst-out : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : f x == b} {v : f y == b}
  → (u == v [ (λ x → f x == b) ↓ p ])
  → u == (ap f p ∘' v)
↓-app='cst-out {p = refl} refl = ! (refl-left-unit _)

↓-cst='app-in : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
  → (u ∘' ap f p) == v
  → (u == v [ (λ x → b == f x) ↓ p ])
↓-cst='app-in {p = refl} refl = refl

↓-cst='app-out : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} {b : B}
  {x y : A} {p : x == y} {u : b == f x} {v : b == f y}
  → (u == v [ (λ x → b == f x) ↓ p ])
  → (u ∘' ap f p) == v
↓-cst='app-out {p = refl} refl = refl

↓-='-in : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B}
  {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
  → (u ∘ ap g p) == (ap f p ∘' v)
  → (u == v [ (λ x → f x == g x) ↓ p ])
↓-='-in {p = refl} q = ! (refl-right-unit _) ∘ (q ∘ refl-left-unit _)

-- Dependent vs nondependent whiskering
-- This definitional behaviour make [↓-=-in] slightly more complicated to prove
-- but [↓-=-in] is often used in the case where [u] and [v] are [refl]
_▹_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u : B x}
  {v w : B y} {p : x == y}
  → (u == v [ B ↓ p ]) → v == w
     → (u == w [ B ↓ p ])
_▹_ {p = refl} q refl = q

refl▹ : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v == w)
  → _▹_ {B = B} {p = refl} refl q == q
refl▹ refl = refl

_◃_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u v : B x}
  {w : B y} {p : x == y}
  → (u == v → (v == w [ B ↓ p ])
     → (u == w [ B ↓ p ]))
_◃_ {p = refl} refl q = q

◃refl : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v == w)
  → _◃_ {B = B} {p = refl} q refl == q
◃refl refl = refl


↓-=-in : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u ◃ apd f p) == (apd g p ▹ v)
  → (u == v [ (λ x → g x == f x) ↓ p ])
↓-=-in {B = B} {p = refl} {u} {v} q =
  ! (◃refl {B = B} u) ∘ (q ∘ refl▹ {B = B} v)

postulate
 ↓-=-out : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B}
  {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
  → (u == v [ (λ x → g x == f x) ↓ p ])
  → (u ◃ apd f p) == (apd g p ▹ v)
--↓-=-out {B = B} {p = refl} refl = {!!}

{- Not used yet

apdd-cst : ∀ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k}
  (g : (a : A) → Π B (C a)) {x y : A} (p : x ≡ y)
  {u v : B} (q : u ≡ v) {r : u ≡[ (λ _ → B) ↓ p ] v} (α : ↓-cst-in p q ≡ r)
  → apdd (λ {a} b → g a b) p r ≡ apd (uncurry g) (Σ-eq p r)
apdd-cst g refl refl refl = refl
-}
-- This one seems a bit weird
↓-apd-out : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k)
  (f : Π A B) {x y : A} (p : x == y)
  {u : C x (f x)} {v : C y (f y)}
  → u == v [ uncurry C ↓ Σ-eq p (apd f p) ]
  → u == v [ (λ z → C z (f z)) ↓ p ]
↓-apd-out C f refl refl = refl
{-
-- Dependent paths over [ap f p]
module _ {i j k} {A : Set i} {B : Set j} (C : B → Set k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x ≡ y} {u : C (f x)} {v : C (f y)}
    → u ≡[ C ◯ f ↓ p ] v
    → u ≡[ C ↓ ap f p ] v
  ↓-ap-in {p = refl} refl = refl

  ↓-ap-out : {x y : A} (p : x ≡ y) {u : C (f x)} {v : C (f y)}
    → u ≡[ C ↓ ap f p ] v
    → u ≡[ C ◯ f ↓ p ] v
  ↓-ap-out refl refl = refl

--  ↓-ap-β

ap-, : ∀ {i j k} {A : Set i} {B : Set j} {C : B → Set k}
  (f : A → B) (g : (a : A) → C (f a)) {x y : A} (p : x ≡ y)
  → ap (λ x → _,_ {P = C} (f x) (g x)) p
       ≡ Σ-eq (ap f p) (↓-ap-in C f (apd g p))
ap-, f g refl = refl
-}

-- Special case of [ap-,]
ap-cst,id : ∀ {i j} {A : Set i} (B : A → Set j)
  {a : A} {x y : B a} (p : x == y)
  → ap (λ x → _,_ {P = B} a x) p == Σ-eq refl p
ap-cst,id B refl = refl

-- apd-nd : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
--   → (p : x ≡ y) → apd f p ≡ ↓-cst-in p (ap f p)
-- apd-nd f refl = refl

apd-◯ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (f : Π A B) (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x == y)
  → apd (g ◯ f) p == ↓-apd-out C f p (apdd g p (apd f p))
apd-◯ f g refl = refl

{- Not used yet

-- apd-apd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
--   (g : (u : Σ A B) → C (π₁ u) (π₂ u)) (f : Π A B) {x y : A} (p : x ≡ y)
--   → apd g (Σ-eq p (apd f p)) ≡ {!↓-ap-in!}
-- apd-apd = {!!}


apd-π₁-β : ∀ {i j} {A : Set i} {B : A → Set j} {x x' : A} (p : x ≡ x')
  {y : B x} {y' : B x'} (q : y ≡[ B ↓ p ] y')
  → ap π₁ (Σ-eq p q) ≡ p
apd-π₁-β refl refl = refl

apd-π₂-β : ∀ {i j} {A : Set i} {B : A → Set j} {x x' : A} (p : x ≡ x')
  {y : B x} {y' : B x'} (q : y ≡[ B ↓ p ] y')
  → apd π₂ (Σ-eq p q) ≡ ↓-ap-out B π₁ (Σ-eq p q)
    (transport (λ p → y ≡[ B ↓ p ] y') (! (apd-π₁-β p q)) q)
apd-π₂-β refl refl = refl
-}

-- Dependent path in a type of the form [λ x → g (f x) ≡ x]
module _ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) where
  ↓-◯=id-in : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → ((ap g (ap f p) ∘' v) == (u ∘ p))
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-◯=id-in {p = refl} q = ! (refl-right-unit _) ∘ (! q ∘ refl-left-unit _)

-- WIP, derive it from more primitive principles
-- ↓-◯≡id-in f g {p = p} {u} {v} q =
--   ↓-≡-in (u ◃ apd (λ x → g (f x)) p ≡⟨ apd-◯ f g p |in-ctx (λ t → u ◃ t) ⟩
--         u ◃ ↓-apd-out _ f p (apdd g p (apd f p)) ≡⟨ apdd-cst (λ _ b → g b) p (ap f p) (! (apd-nd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (apd (λ t → g (π₂ t)) (Σ-eq p (apd f p))) ≡⟨ apd-◯ π₂ g (Σ-eq p (apd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (↓-apd-out _ π₂ (Σ-eq p (apd f p)) (apdd g (Σ-eq p (apd f p)) (apd π₂ (Σ-eq p (apd f p))))) ≡⟨ {!!} ⟩
--         apd (λ x → x) p ▹ v ∎)

ua-in : ∀ {i} {A B : Set i} → A ≃ B → A == B
ua-in = eq-to-path

ua-out : ∀ {i} {A B : Set i} → A == B → A ≃ B
ua-out = path-to-eq

ua-β : ∀ {i} {A B : Set i} (e : A ≃ B)
  → ua-out (ua-in e) == e
ua-β e = eq-to-path-right-inverse e

-- These lemmas do not really look computational, but they are only used in the
-- [↓-pp] lemmas which do look computational.

to-transp-in : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  → (π₁ (ua-out (ap B p)) u == v)
  → (u == v [ B ↓ p ])
to-transp-in B refl refl = refl

to-transp-out : ∀ {i j} {A : Set i} {B : A → Set j}
  {a a' : A} {p : a == a'}
  {u : B a} {v : B a'}
  → (u == v [ B ↓ p ])
  → (π₁ (ua-out (ap B p)) u == v)
to-transp-out {p = refl} refl = refl

to-transp-β : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a == a')
  {u : B a} {v : B a'}
  (q : π₁ (ua-out (ap B p)) u == v)
  → to-transp-out (to-transp-in B p q) == q
to-transp-β B refl refl = refl


-- Stuff that do not belong here

ap-∘' : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
  {x y z : A} (p : x == y) (q : y == z)
  → ap f (p ∘' q) == (ap f p ∘' ap f q)
ap-∘' f refl refl = refl

-- Dependent concatenation'
_∘'dep_ : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  → (u == v [ B ↓ p ]
   → v == w [ B ↓ p' ]
   → u == w [ B ↓ (p ∘' p') ])
_∘'dep_ {p' = refl} q refl = q

-- Implementation of [_∘'_] on Σ
Σ-∘' : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x == y} {p' : y == z}
  {u : B x} {v : B y} {w : B z}
  (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
  → (Σ-eq p q ∘' Σ-eq p' r) == Σ-eq (p ∘' p') (q ∘'dep r)
Σ-∘' {p' = refl} q refl = refl

-- No idea what that is
to-transp-weird : ∀ {i j} {A : Set i} {B : A → Set j}
  {u v : A} {d : B u} {d' d'' : B v} {p : u == v}
  (q : d == d' [ B ↓ p ]) (r : π₁ (ua-out (ap B p)) d == d'')
  → (to-transp-in B p r ∘'dep (! r ∘ to-transp-out q)) == q
to-transp-weird {p = refl} refl refl = refl


_∘'2_ : ∀ {i j} {A : Set i} {B : A → Set j} {a b c : Π A B}
  {x y : A} {p : x == y} {q : a x == b x} {q' : a y == b y}
  {r : b x == c x} {r' : b y == c y}
  → (q == q'            [ (λ z → a z == b z) ↓ p ])
  → (r == r'            [ (λ z → b z == c z) ↓ p ])
  → (q ∘' r == q' ∘' r' [ (λ z → a z == c z) ↓ p ])
_∘'2_ {p = refl} refl refl = refl

stuff : ∀ {i j} {A : Set i} {B : Set j} {b : B} {c : A → B} {d : A → B}
  (q : (a : A) → b == c a) (r : (a : A) → c a == d a) {a a' : A} (p : a == a')
  → apd (λ a → q a ∘' r a) p == ((apd q p) ∘'2 (apd r p))
stuff q r refl = refl


apd= : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B} (q : (x : A) → f x == g x) {x y : A} (p : x == y)
--    → (q x == q y [ (λ z → f z == g z) ↓ p ])
  → (apd f p ▹ q y) == (q x ◃ apd g p)
apd= q p = ! (↓-=-out (apd q p))
--apd= q refl =
