{-# OPTIONS --without-K #-}

-- Drop-in replacement for the module [Base].
module BaseOver where

-- We hide [apd] and [Σ-eq] because their type is not correct, we want to use
-- dependent paths instead
open import Base public hiding (apd; Σ-eq)

-- Notion of path over a path
path-over : ∀ {i j} {A : Set i} (B : A → Set j)
  {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Set j
path-over B refl u v = (u ≡ v)

syntax path-over B p u v =
  u ≡[ B ↓ p ] v

-- New apd
apd : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) {x y : A}
  → (p : x ≡ y) → f x ≡[ B ↓ p ] f y
apd f refl = refl

-- Σ-types are used to simulate telescopes and to be able to only use the
-- notion of path over a single path

-- Intro for paths in a Σ
Σ-eq : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} (p : x ≡ y)
  {u : B x} {v : B y} (q : u ≡[ B ↓ p ] v)
  → (x , u) ≡ (y , v)
Σ-eq refl refl = refl

{- Not used yet
apdd : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x ≡ y)
  {u : B x} {v : B y} (q : u ≡[ B ↓ p ] v)
  → g u ≡[ uncurry C ↓ Σ-eq p q ] g v
apdd g refl refl = refl

-- Not used yet
↓refl-in : ∀ {i j} {A : Set i} {B : A → Set j}
  {x : A} {u v : B x} (p : u ≡ v)
  → u ≡[ B ↓ refl ] v
↓refl-in refl = refl
-}

-- Dependent paths in a constant fibration
module _ {i j} {A : Set i} {B : Set j} where

  ↓-cst-in : {x y : A} (p : x ≡ y) {u v : B}
    → u ≡ v
    → u ≡[ (λ _ → B) ↓ p ] v
  ↓-cst-in refl q = q

  ↓-cst-out : {x y : A} {p : x ≡ y} {u v : B}
    → u ≡[ (λ _ → B) ↓ p ] v
    → u ≡ v
  ↓-cst-out {p = refl} q = q

  ↓-cst-β : {x y : A} (p : x ≡ y) {u v : B} (q : u ≡ v)
    → (↓-cst-out (↓-cst-in p q) ≡ q)
  ↓-cst-β refl q = refl

-- -- ap can be defined via apd, not sure whether it’s a good idea or not
-- ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
--   → f x ≡ f y
-- ap f p = ↓-cst-out (apd f p)

-- Dependent paths in a Π-type
module _ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k} where

  ↓-Π-in : {x x' : A} {p : x ≡ x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → ({t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
        → u t ≡[ uncurry C ↓ Σ-eq p q ] u' t')
    → (u ≡[ (λ x → Π (B x) (C x)) ↓ p ] u')
  ↓-Π-in {p = refl} f = funext (λ x → f (refl {a = x}))

  ↓-Π-out : {x x' : A} {p : x ≡ x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (u ≡[ (λ x → Π (B x) (C x)) ↓ p ] u')
    → ({t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
        → u t ≡[ uncurry C ↓ Σ-eq p q ] u' t')
  ↓-Π-out {p = refl} q refl = happly q _

  ↓-Π-β : {x x' : A} {p : x ≡ x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (f : {t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
            → u t ≡[ uncurry C ↓ Σ-eq p q ] u' t')
    → {t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
    → ↓-Π-out (↓-Π-in f) q ≡ f q
  ↓-Π-β {p = refl} f refl = happly (happly-funext (λ x → f (refl {a = x}))) _

-- Dependent paths in a Π-type where the codomain is not dependent on anything
module _ {i j k} {A : Set i} {B : A → Set j} {C : Set k} {x x' : A} {p : x ≡ x'}
  {u : B x → C} {u' : B x' → C} where

  ↓-app→cst-in :
    ({t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
      → u t ≡ u' t')
    → (u ≡[ (λ x → B x → C) ↓ p ] u')
  ↓-app→cst-in f = ↓-Π-in (λ q → ↓-cst-in (Σ-eq p q) (f q))

  ↓-app→cst-out :
    (u ≡[ (λ x → B x → C) ↓ p ] u')
    → ({t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
        → u t ≡ u' t')
  ↓-app→cst-out r q = ↓-cst-out (↓-Π-out r q)

  ↓-app→cst-β :
    (f : ({t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
           → u t ≡ u' t'))
    → {t : B x} {t' : B x'} (q : t ≡[ B ↓ p ] t')
    → ↓-app→cst-out (↓-app→cst-in f) q ≡ f q
  ↓-app→cst-β f q =
    ↓-app→cst-out (↓-app→cst-in f) q
             ≡⟨ refl ⟩
    ↓-cst-out (↓-Π-out (↓-Π-in (λ qq → ↓-cst-in (Σ-eq p qq) (f qq))) q)
             ≡⟨ ↓-Π-β (λ qq → ↓-cst-in (Σ-eq p qq) (f qq)) q |in-ctx ↓-cst-out ⟩
    ↓-cst-out (↓-cst-in (Σ-eq p q) (f q))
             ≡⟨ ↓-cst-β (Σ-eq p q) (f q) ⟩
    f q ∎

split-ap2 : ∀ {i j k} {A : Set i} {B : A → Set j} {C : Set k} (f : Σ A B → C)
  {x y : A} (p : x ≡ y)
  {u : B x} {v : B y} (q : u ≡[ B ↓ p ] v)
  → ap f (Σ-eq p q) ≡ ↓-app→cst-out (apd (curry f) p) q
split-ap2 f refl refl = refl

{- Not used yet
-- Dependent vs nondependent whiskering
-- This definitional behaviour make [↓-≡-in] slightly more complicated to prove
-- but [↓-≡-in] is often used in the case where [u] and [v] are [refl]
_▹_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u : B x}
  {v w : B y} {p : x ≡ y}
  → ((u ≡[ B ↓ p ] v) → v ≡ w
     → (u ≡[ B ↓ p ] w))
_▹_ {p = refl} q refl = q

refl▹ : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v ≡ w)
  → _▹_ {B = B} {p = refl} refl q ≡ q
refl▹ refl = refl

_◃_ : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {u v : B x}
  {w : B y} {p : x ≡ y}
  → (u ≡ v → (v ≡[ B ↓ p ] w)
     → (u ≡[ B ↓ p ] w))
_◃_ {p = refl} refl q = q

◃refl : ∀ {i j} {A : Set i} {B : A → Set j} {x : A}
  {v w : B x} (q : v ≡ w)
  → _◃_ {B = B} {p = refl} q refl ≡ q
◃refl refl = refl


↓-≡-in : ∀ {i j} {A : Set i} {B : A → Set j} {f g : Π A B}
  {x y : A} {p : x ≡ y} {u : g x ≡ f x} {v : g y ≡ f y}
  → u ◃ apd f p ≡ apd g p ▹ v
  → (u ≡[ (λ x → g x ≡ f x) ↓ p ] v)
↓-≡-in {B = B} {p = refl} {u} {v} q =
  ! (◃refl {B = B} u) ∘ (q ∘ refl▹ {B = B} v)

apdd-cst : ∀ {i j k} {A : Set i} {B : Set j} {C : A → B → Set k}
  (g : (a : A) → Π B (C a)) {x y : A} (p : x ≡ y)
  {u v : B} (q : u ≡ v) {r : u ≡[ (λ _ → B) ↓ p ] v} (α : ↓-cst-in p q ≡ r)
  → apdd (λ {a} b → g a b) p r ≡ apd (uncurry g) (Σ-eq p r)
apdd-cst g refl refl refl = refl

-- This one seems a bit weird
↓-apd-out : ∀ {i j k} {A : Set i} {B : A → Set j} (C : (a : A) → B a → Set k)
  (f : Π A B) {x y : A} (p : x ≡ y)
  {u : C x (f x)} {v : C y (f y)}
  → u ≡[ uncurry C ↓ Σ-eq p (apd f p) ] v
  → u ≡[ (λ z → C z (f z)) ↓ p ] v
↓-apd-out C f refl refl = refl

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
  {a : A} {x y : B a} (p : x ≡ y)
  → ap (λ x → _,_ {P = B} a x) p ≡ Σ-eq refl p
ap-cst,id B refl = refl

{- Not used yet
apd-nd : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (p : x ≡ y) → apd f p ≡ ↓-cst-in p (ap f p)
apd-nd f refl = refl

-- Not good
apd-◯ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
  (f : Π A B) (g : {a : A} → Π (B a) (C a)) {x y : A} (p : x ≡ y)
  → apd (g ◯ f) p ≡ ↓-apd-out C f p (apdd g p (apd f p))
apd-◯ f g refl = refl

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
  ↓-◯≡id-in : {x y : A} {p : x ≡ y} {u : g (f x) ≡ x} {v : g (f y) ≡ y}
    → (ap g (ap f p) ∘' v ≡ u ∘ p)
    → (u ≡[ (λ x → g (f x) ≡ x) ↓ p ] v)
  ↓-◯≡id-in {p = refl} q = ! (refl-right-unit _) ∘ (! q ∘ refl-left-unit _)

-- WIP, derive it from more primitive principles
-- ↓-◯≡id-in f g {p = p} {u} {v} q =
--   ↓-≡-in (u ◃ apd (λ x → g (f x)) p ≡⟨ apd-◯ f g p |in-ctx (λ t → u ◃ t) ⟩
--         u ◃ ↓-apd-out _ f p (apdd g p (apd f p)) ≡⟨ apdd-cst (λ _ b → g b) p (ap f p) (! (apd-nd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (apd (λ t → g (π₂ t)) (Σ-eq p (apd f p))) ≡⟨ apd-◯ π₂ g (Σ-eq p (apd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (↓-apd-out _ π₂ (Σ-eq p (apd f p)) (apdd g (Σ-eq p (apd f p)) (apd π₂ (Σ-eq p (apd f p))))) ≡⟨ {!!} ⟩
--         apd (λ x → x) p ▹ v ∎)

ua-in : ∀ {i} {A B : Set i} → A ≃ B → A ≡ B
ua-in = eq-to-path

ua-out : ∀ {i} {A B : Set i} → A ≡ B → A ≃ B
ua-out = path-to-eq

ua-β : ∀ {i} {A B : Set i} (e : A ≃ B)
  → ua-out (ua-in e) ≡ e
ua-β e = eq-to-path-right-inverse e

-- These lemmas do not really look computational, but they are only used in the
-- [↓-pp] lemmas which do look computational.

to-transp-in : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a ≡ a')
  {u : B a} {v : B a'}
  → (π₁ (ua-out (ap B p)) u ≡ v)
  → (u ≡[ B ↓ p ] v)
to-transp-in B refl refl = refl

to-transp-out : ∀ {i j} {A : Set i} {B : A → Set j}
  {a a' : A} {p : a ≡ a'}
  {u : B a} {v : B a'}
  → (u ≡[ B ↓ p ] v)
  → (π₁ (ua-out (ap B p)) u ≡ v)
to-transp-out {p = refl} refl = refl

to-transp-β : ∀ {i j} {A : Set i} (B : A → Set j)
  {a a' : A} (p : a ≡ a')
  {u : B a} {v : B a'}
  (q : π₁ (ua-out (ap B p)) u ≡ v)
  → to-transp-out (to-transp-in B p q) ≡ q
to-transp-β B refl refl = refl


-- Stuff that do not belong here

ap-∘' : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
  {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → ap f (p ∘' q) ≡ ap f p ∘' ap f q
ap-∘' f refl refl = refl

-- Dependent concatenation'
_∘'dep_ : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x ≡ y} {p' : y ≡ z}
  {u : B x} {v : B y} {w : B z}
  → (u ≡[ B ↓ p ] v
   → v ≡[ B ↓ p' ] w
   → u ≡[ B ↓ (p ∘' p') ] w)
_∘'dep_ {p' = refl} q refl = q

-- Implementation of [_∘'_] on Σ
Σ-∘' : ∀ {i j} {A : Set i} {B : A → Set j}
  {x y z : A} {p : x ≡ y} {p' : y ≡ z}
  {u : B x} {v : B y} {w : B z}
  (q : u ≡[ B ↓ p ] v) (r : v ≡[ B ↓ p' ] w)
  → Σ-eq p q ∘' Σ-eq p' r ≡ Σ-eq (p ∘' p') (q ∘'dep r)
Σ-∘' {p' = refl} q refl = refl

-- No idea what that is
to-transp-weird : ∀ {i j} {A : Set i} {B : A → Set j}
  {u v : A} {d : B u} {d' d'' : B v} {p : u ≡ v}
  (q : d ≡[ B ↓ p ] d'') (r : π₁ (ua-out (ap B p)) d ≡ d')
  → to-transp-in B p r ∘'dep (! r ∘ to-transp-out q) ≡ q
to-transp-weird {p = refl} refl refl = refl
