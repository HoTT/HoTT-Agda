{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Paths

module lib.types.Pi where

instance
  Π-level : ∀ {i j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
    → ((x : A) → has-level n (B x)) → has-level n (Π A B)
  Π-level {n = ⟨-2⟩} p = has-level-in ((λ x → contr-center (p x)) , lemma)
    where abstract lemma = λ f → λ= (λ x → contr-path (p x) (f x))
  Π-level {n = S n} p = has-level-in lemma where
    abstract
      lemma = λ f g →
        equiv-preserves-level λ=-equiv {{Π-level (λ x → has-level-apply (p x) (f x) (g x))}}

  Πi-level : ∀ {i j} {A : Type i} {B : A → Type j} {n : ℕ₋₂}
    → ((x : A) → has-level n (B x)) → has-level n ({x : A} → B x)
  Πi-level {A = A} {B} p = equiv-preserves-level e {{Π-level p}}  where

    e : Π A B ≃ ({x : A} → B x)
    fst e f {x} = f x
    is-equiv.g (snd e) f x = f
    is-equiv.f-g (snd e) _ = idp
    is-equiv.g-f (snd e) _ = idp
    is-equiv.adj (snd e) _ = idp


{- Equivalences in a Π-type -}
Π-emap-l : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k)
            → (e : A ≃ B) → Π A (P ∘ –> e) ≃ Π B P
Π-emap-l {A = A} {B = B} P e = equiv f g f-g g-f where
  f : Π A (P ∘ –> e) → Π B P
  f u b = transport P (<–-inv-r e b) (u (<– e b))

  g : Π B P → Π A (P ∘ –> e)
  g v a = v (–> e a)

  abstract
    f-g : ∀ v → f (g v) == v
    f-g v = λ= λ b → to-transp (apd v (<–-inv-r e b))

    g-f : ∀ u → g (f u) == u
    g-f u = λ= λ a → to-transp $ transport (λ p → u _ == _ [ P ↓ p ])
                                           (<–-inv-adj e a)
                                           (↓-ap-in P (–> e)
                                                      (apd u $ <–-inv-l e a))

Π-emap-r : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  → (∀ x → B x ≃ C x) → Π A B ≃ Π A C
Π-emap-r {A = A} {B = B} {C = C} k = equiv f g f-g g-f
  where f : Π A B → Π A C
        f c x = –> (k x) (c x)

        g : Π A C → Π A B
        g d x = <– (k x) (d x)

        abstract
          f-g : ∀ d → f (g d) == d
          f-g d = λ= (λ x →  <–-inv-r (k x) (d x))

          g-f : ∀ c → g (f c) == c
          g-f c = λ= (λ x → <–-inv-l (k x) (c x))

{-
favonia: This part is not used.

module _ {i₀ i₁ j₀ j₁} {A₀ : Type i₀} {A₁ : Type i₁}
         {B₀ : A₀ → Type j₀} {B₁ : A₁ → Type j₁} where
  Π-emap : (u : A₀ ≃ A₁) (v : ∀ a → B₀ (<– u a) ≃ B₁ a) → Π A₀ B₀ ≃ Π A₁ B₁
  Π-emap u v = Π A₀ B₀           ≃⟨ Π-emap-l _ (u ⁻¹) ⁻¹ ⟩
               Π A₁ (B₀ ∘ <– u)  ≃⟨ Π-emap-r v ⟩
               Π A₁ B₁           ≃∎

  Π-emap' : (u : A₀ ≃ A₁) (v : ∀ a → B₀ a ≃ B₁ (–> u a)) → Π A₀ B₀ ≃ Π A₁ B₁
  Π-emap' u v = Π A₀ B₀           ≃⟨ Π-emap-r v ⟩
                Π A₀ (B₁ ∘ –> u)  ≃⟨ Π-emap-l _ u ⟩
                Π A₁ B₁           ≃∎
-}


{- Coversions between functions with implicit and explicit arguments -}

expose-equiv : ∀ {i j} {A : Type i} {B : A → Type j}
  → ({x : A} → B x) ≃ ((x : A) → B x)
expose-equiv = (λ f a → f {a}) , is-eq
  _
  (λ f {a} → f a)
  (λ _ → idp)
  (λ _ → idp)



{- Dependent paths in a Π-type -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
  where

  ↓-Π-in : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ pair= p q ])
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
  ↓-Π-in {p = idp} f = λ= (λ x → f (idp {a = x}))

  ↓-Π-out : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ pair= p q ])
  ↓-Π-out {p = idp} q idp = app= q _

  ↓-Π-β : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (f : {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
            → u t == u' t' [ uncurry C ↓ pair= p q ])
    → {t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
    → ↓-Π-out (↓-Π-in f) q == f q
  ↓-Π-β {p = idp} f idp = app=-β (λ x → f (idp {a = x})) _

  ↓-Π-η : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → (q : (u == u' [ (λ x → Π (B x) (C x)) ↓ p ]))
    → ↓-Π-in (↓-Π-out q) == q
  ↓-Π-η {p = idp} q = ! (λ=-η q)

  ↓-Π-equiv : {x x' : A} {p : x == x'} {u : Π (B x) (C x)} {u' : Π (B x') (C x')}
    → ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
        → u t == u' t' [ uncurry C ↓ pair= p q ])
    ≃ (u == u' [ (λ x → Π (B x) (C x)) ↓ p ])
  ↓-Π-equiv {p = idp} = equiv ↓-Π-in ↓-Π-out ↓-Π-η
    (λ u → <– (ap-equiv expose-equiv _ _)
      (λ= (λ t → <– (ap-equiv expose-equiv _ _)
        (λ= (λ t' → λ= (↓-Π-β u))))))

{- Dependent paths in a Π-type where the codomain is not dependent on anything

Right now, this is defined in terms of the previous one. Maybe it’s a good idea,
maybe not.
-}
module _ {i j k} {A : Type i} {B : A → Type j} {C : Type k} {x x' : A}
  {p : x == x'} {u : B x → C} {u' : B x' → C} where

  ↓-app→cst-in :
    ({t : B x} {t' : B x'} (q : t == t' [ B ↓ p ])
      → u t == u' t')
    → (u == u' [ (λ x → B x → C) ↓ p ])
  ↓-app→cst-in f = ↓-Π-in (λ q → ↓-cst-in (f q))

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
    ↓-cst-out (↓-Π-out (↓-Π-in (λ qq → ↓-cst-in (f qq))) q)
             =⟨ ↓-Π-β (λ qq → ↓-cst-in (f qq)) q |in-ctx
                      ↓-cst-out ⟩
    ↓-cst-out (↓-cst-in {p = pair= p q} (f q))
             =⟨ ↓-cst-β (pair= p q) (f q) ⟩
    f q =∎

{- favonia: these lemmas are not used anywhere

{- Similar to above, with domain being the identity function. -}
{- These lemmas were in homotopy.FunctionOver and in different conventions. -}

module _ {i j} {A B : Type i} {C : Type j}
  {u : A → C} {v : B → C} where

  ↓-idf→cst-in : ∀ (p : A == B)
    → u == v ∘ coe p
    → u == v [ (λ x → x → C) ↓ p ]
  ↓-idf→cst-in idp q = q

  ↓-idf→cst-ua-in : ∀ (e : A ≃ B)
    → u == v ∘ –> e
    → u == v [ (λ x → x → C) ↓ ua e ]
  ↓-idf→cst-ua-in e q = ↓-idf→cst-in (ua e) (q ∙ ap (v ∘_) (λ= λ a → ! (coe-β e a)))

  ↓-idf→cst-in' : ∀ (p : A == B)
    → u ∘ coe! p == v
    → u == v [ (λ x → x → C) ↓ p ]
  ↓-idf→cst-in' idp q = q

  ↓-idf→cst-ua-in' : ∀ (e : A ≃ B)
    → u ∘ <– e == v
    → u == v [ (λ x → x → C) ↓ ua e ]
  ↓-idf→cst-ua-in' e q = ↓-idf→cst-in' (ua e) (ap (u ∘_) (λ= λ a → coe!-β e a) ∙ q)

module _ {i j} {A B : Type i} {C : Type j}
  {u : C → A} {v : C → B} where

  ↓-cst→idf-in : ∀ (p : A == B)
    → coe p ∘ u == v
    → u == v [ (λ x → C → x) ↓ p ]
  ↓-cst→idf-in idp q = q

  ↓-cst→idf-ua-in : ∀ (e : A ≃ B)
    → –> e ∘ u == v
    → u == v [ (λ x → C → x) ↓ ua e ]
  ↓-cst→idf-ua-in e q = ↓-cst→idf-in (ua e) (ap (_∘ u) (λ= λ a → coe-β e a) ∙ q)

  ↓-cst→idf-in' : ∀ (p : A == B)
    → u == coe! p ∘ v
    → u == v [ (λ x → C → x) ↓ p ]
  ↓-cst→idf-in' idp q = q

  ↓-cst→idf-ua-in' : ∀ (e : A ≃ B)
    → u == <– e ∘ v
    → u == v [ (λ x → C → x) ↓ ua e ]
  ↓-cst→idf-ua-in' e q = ↓-cst→idf-in' (ua e) (q ∙ ap (_∘ v) (λ= λ a → ! (coe!-β e a)))
-}

{- Dependent paths in an arrow type -}
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

{- Transport form of dependent path in an arrow type -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} where

  ↓-→-from-transp : {x x' : A} {p : x == x'}
    {u : B x → C x} {u' : B x' → C x'}
    → transport C p ∘ u == u' ∘ transport B p
    → u == u' [ (λ x → B x → C x) ↓ p ]
  ↓-→-from-transp {p = idp} q = q

  comp-transp : {x x' x'' : A}
    {u : B x → C x} {u' : B x' → C x'} {u'' : B x'' → C x''}
    (p : x == x') (q : x' == x'')
    (r : transport C p ∘ u == u' ∘ transport B p)
    (s : transport C q ∘ u' == u'' ∘ transport B q)
    → transport C (p ∙ q) ∘ u ∼ u'' ∘ transport B (p ∙ q)
  comp-transp {x} {x'} {x''} {u} {u'} {u''} p q r s b =
    transp-∙ p q (u b)
      ∙ ap (transport C q) (app= r b)
      ∙ app= s (transport B p b)
      ∙ ! (ap u'' (transp-∙ p q b))

  ↓-→-from-transp-∙ᵈ : {x x' x'' : A} {p : x == x'} {q : x' == x''}
    {u : B x → C x} {u' : B x' → C x'} {u'' : B x'' → C x''}
    (r : transport C p ∘ u == u' ∘ transport B p)
    (s : transport C q ∘ u' == u'' ∘ transport B q)
    → ↓-→-from-transp {x} {x''} {p ∙ q} {u} {u''} (λ= (comp-transp {x} {x'} {x''} {u} {u'} {u''} p q r s)) ==
      ↓-→-from-transp {x} {x'} {p = p} r ∙ᵈ ↓-→-from-transp {x'} {x''} {q} s
  ↓-→-from-transp-∙ᵈ {p = idp} {q = idp} idp idp = ! (λ=-η idp)

  ↓-→-to-transp : {x x' : A} {p : x == x'}
    {u : B x → C x} {u' : B x' → C x'}
    → u == u' [ (λ x → B x → C x) ↓ p ]
    → transport C p ∘ u == u' ∘ transport B p
  ↓-→-to-transp {p = idp} q = q

-- Dependent paths in a Π-type where the domain is constant
module _ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k} where

  ↓-Π-cst-app-in : {x x' : A} {p : x == x'}
    {u : (b : B) → C x b} {u' : (b : B) → C x' b}
    → ((b : B) → u b == u' b [ (λ x → C x b) ↓ p ])
    → (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
  ↓-Π-cst-app-in {p = idp} f = λ= f

  ↓-Π-cst-app-out : {x x' : A} {p : x == x'}
    {u : (b : B) → C x b} {u' : (b : B) → C x' b}
    → (u == u' [ (λ x → (b : B) → C x b) ↓ p ])
    → ((b : B) → u b == u' b [ (λ x → C x b) ↓ p ])
  ↓-Π-cst-app-out {p = idp} q = app= q

split-ap2 : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Type k} (f : Σ A B → C)
  {x y : A} (p : x == y)
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → ap f (pair= p q) == ↓-app→cst-out (apd (curry f) p) q
split-ap2 f idp idp = idp

{-
Interaction of [apd] with function composition.
The basic idea is that [apd (g ∘ f) p == apd g (apd f p)] but the version here
is well-typed. Note that we assume a propositional equality [r] between
[apd f p] and [q].
-}
apd-∘ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
  (g : {a : A} → Π (B a) (C a)) (f : Π A B) {x y : A} (p : x == y)
  {q : f x == f y [ B ↓ p ]} (r : apd f p == q)
  → apd (g ∘ f) p == ↓-apd-out C r (apd↓ g q)
apd-∘ g f idp idp = idp

{- When [g] is nondependent, it’s much simpler -}
apd-∘' : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (g : {a : A} → B a → C a) (f : Π A B) {x y : A} (p : x == y)
  → apd (g ∘ f) p == ap↓ g (apd f p)
apd-∘' g f idp = idp

∘'-apd : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (g : {a : A} → B a → C a) (f : Π A B) {x y : A} (p : x == y)
  → ap↓ g (apd f p) == apd (g ∘ f) p
∘'-apd g f idp = idp

{- And when [f] is nondependent, it’s also a bit simpler -}
apd-∘'' : ∀ {i j k} {A : Type i} {B : Type j} {C : (b : B) → Type k}
  (g : Π B C) (f : A → B) {x y : A} (p : x == y)
  {q : f x == f y} (r : ap f p == q)
  → apd (g ∘ f) p == ↓-ap-out= C f p r (apd g q) --(apd↓ g q)
apd-∘'' g f idp idp = idp

→-transp : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  {a₀ a₁ : A} (p : a₀ == a₁)
  (g : B a₀ → C a₀)
  → transport (λ a → B a → C a) p g ==
    transport C p ∘ g ∘ transport! B p
→-transp p@idp g = idp

Π-transp : ∀ {i j k} {A : Type i} {B : Type j} {C : A → B → Type k}
  {a₀ a₁ : A} (p : a₀ == a₁)
  (g : (b : B) → C a₀ b)
  → transport (λ a → ∀ b → C a b) p g ==
    λ b → transport (λ a → C a b) p (g b)
Π-transp p@idp g = idp

{- 2-dimensional coherence conditions -}

-- lhs :
--   ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} {f g : Π A B}
--   {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--   (k : (u ◃ apd g p) == (apd f p ▹ v))
--   (h : {a : A} → B a → C a)
--   → ap h u ◃ apd (h ∘ g) p == ap↓ h (u ◃ apd g p)

-- rhs :
--   ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} {f g : Π A B}
--   {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--   (k : (u ◃ apd g p) == (apd f p ▹ v))
--   (h : {a : A} → B a → C a)
--   → ap↓ h (apd f p ▹ v) == apd (h ∘ f) p ▹ ap h v

-- ap↓-↓-=-in :
--   ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} {f g : Π A B}
--   {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
--   (k : (u ◃ apd g p) == (apd f p ▹ v))
--   (h : {a : A} → B a → C a)
--   → ap↓ (λ {a} → ap (h {a = a})) (↓-=-in {p = p} {u = u} {v = v} k)
--   == ↓-=-in (lhs {f = f} {g = g} k h ∙ ap (ap↓ (λ {a} → h {a = a})) k
--                                      ∙ rhs {f = f} {g = g} k h)

{-
Commutation of [ap↓ (ap h)] and [↓-swap!]. This is "just" J, but it’s not as
easy as it seems.
-}

-- module Ap↓-swap! {i j k ℓ} {A : Type i} {B : Type j} {C : Type k}
--   {D : Type ℓ} (h : C → D) (f : A → C) (g : B → C)
--   {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
--   (r : f a == g b') (s : f a' == g b)
--   (t : r == s ∙ ap g q  [ (λ x → f x == g b') ↓ p ])
--   where

--   lhs : ap h (ap f p ∙' s) == ap (h ∘ f) p ∙' ap h s
--   lhs = ap-∙' h (ap f p) s ∙ (ap (λ u → u ∙' ap h s) (∘-ap h f p))

--   rhs : ap h (s ∙ ap g q) == ap h s ∙ ap (h ∘ g) q
--   rhs = ap-∙ h s (ap g q) ∙ (ap (λ u → ap h s ∙ u) (∘-ap h g q))

--   β : ap↓ (ap h) (↓-swap! f g r s t) ==
--               lhs ◃ ↓-swap! (h ∘ f) (h ∘ g) (ap h r) (ap h s) (ap↓ (ap h) t ▹ rhs)
--   β with a | a' | p | b | b' | q | r | s | t
--   β | a | .a | idp | b | .b | idp | r | s | t = coh r s t  where

--     T : {x x' : C} (r s : x == x') (t : r == s ∙ idp) → Type _
--     T r s t =
--       ap (ap h) (∙'-unit-l s ∙ ! (∙-unit-r s) ∙ ! t) ==
--       (ap-∙' h idp s ∙ idp)
--       ∙
--       (∙'-unit-l (ap h s) ∙
--       ! (∙-unit-r (ap h s)) ∙
--       !
--       (ap (ap h) t ∙'
--         (ap-∙ h s idp ∙ idp)))

--     coh' : {x x' : C} {r s : x == x'} (t : r == s) → T r s (t ∙ ! (∙-unit-r s))
--     coh' {r = idp} {s = .idp} idp = idp

--     coh : {x x' : C} (r s : x == x') (t : r == s ∙ idp) → T r s t
--     coh r s t = transport (λ t → T r s t) (coh2 t (∙-unit-r s)) (coh' (t ∙ ∙-unit-r s))  where

--       coh2 : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → (p ∙ q) ∙ ! q == p
--       coh2 idp idp = idp


-- module _ {i j k} {A : Type i} {B B' : Type j} {C : Type k} (f : A → C) (g' : B' → B) (g : B → C) where

--   abc : {a a' : A} {p : a == a'} {c c' : B'} {q' : c == c'} {q : g' c == g' c'}
--     (r : f a == g (g' c')) (s : f a' == g (g' c))
--     (t : q == ap g' q')
--     (α : r == s ∙ ap g q [ (λ x → f x == g (g' c')) ↓ p ])
--     → {!(↓-swap! f g r s α ▹ ?) ∙'2ᵈ ?!} == ↓-swap! f (g ∘ g') {p = p} {q = q'} r s (α ▹ ap (λ u → s ∙ u) (ap (ap g) t ∙ ∘-ap g g' q'))
--   abc = {!!}
