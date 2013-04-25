{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Pushout where

record Span (i j k : ULevel) : Type (suc (max (max i j) k)) where
  constructor span
  field
    A : Type i
    B : Type j
    C : Type k
    f : C → A
    g : C → B

private
  span=-raw : ∀ {i j k} {A A' : Type i} (p : A == A')
    {B B' : Type j} (q : B == B') {C C' : Type k} (r : C == C')
    {f : C → A} {f' : C' → A'}
    (s : f == f' [ (λ CA → fst CA → snd CA) ↓ pair=' r p ])
    {g : C → B} {g' : C' → B'}
    (t : g == g' [ (λ CB → fst CB → snd CB) ↓ pair=' r q ])
    → (span A B C f g) == (span A' B' C' f' g')
  span=-raw idp idp idp idp idp = idp

-- TODO
-- span= : ∀ {i j k} {A A' : Type i} (p : A ≃ A')
--   {B B' : Type j} (q : B ≃ B') {C C' : Type k} (r : C ≃ C')
--   {f : C → A} {f' : C' → A'} (s : (a : C) →  f' (fst r a) == (fst p) (f a))
--   {g : C → B} {g' : C' → B'} (t : (b : C) → (fst q) (g b) == g' (fst r b))
--   → (span A B C f g) == (span A' B' C' f' g')
-- span= p q r {f} {f'} s {g} {g'} t = span=-raw
--   (ua p)
--   (ua q)
--   (ua r)
--   (↓-→-in (λ α → {!s!}))
--   (↓-→-in (λ β → {!↓-cst2'-out {B = idf _} (ua r) (ua q) β!}))
--   -- (eq-to-path p)
--   -- (eq-to-path q)
--   -- (eq-to-path r)
--   -- (funext (λ a → ap f' (trans-id-eq-to-path r a)
--   --                    ∘ (s a ∘ ! (trans-id-eq-to-path p (f a)))))
--   -- (funext (λ b → trans-id-eq-to-path q (g b)
--   --                    ∘ (t b ∘ ap g' (! (trans-id-eq-to-path r b)))))

module Pushout {i j k} {d : Span i j k} where

  open Span d

  private
    data #pushout : Type (max (max i j) k) where
      #left : A → #pushout
      #right : B → #pushout

  pushout : Type _
  pushout = #pushout

  left : A → pushout
  left = #left

  right : B → pushout
  right = #right

  postulate  -- HIT
    glue : (c : C) → left (f c) == right (g c)

  pushout-elim : ∀ {l} {P : pushout → Type l} (left* : (a : A) → P (left a))
    (right* : (b : B) → P (right b))
    (glue* : (c : C) → left* (f c) == right* (g c) [ P ↓ glue c ])
    → (x : pushout) → P x
  pushout-elim left* right* glue* (#left y) = left* y
  pushout-elim Pleft* right* glue* (#right y) = right* y

  postulate  -- HIT
    glue-β : ∀ {l} {P : pushout → Type l} (left* : (a : A) → P (left a))
      (right* : (b : B) → P (right b))
      (glue* : (c : C) → left* (f c) == right* (g c) [ P ↓ glue c ])
      (c : C)
        → apd (pushout-elim left* right* glue*) (glue c) == glue* c

  pushout-rec : ∀ {l} {D : Type l} (left* : A → D) (right* : B → D)
    (glue* : (c : C) → left* (f c) == right* (g c)) → (pushout → D)
  pushout-rec left* right* glue* (#left y) = left* y
  pushout-rec left* right* glue* (#right y) = right* y

  postulate  -- HIT
    glue-β' : ∀ {l} {D : Type l} (left* : A → D) (right* : B → D)
      (glue* : (c : C) → left* (f c) == right* (g c)) (c : C)
      → ap (pushout-rec left* right* glue*) (glue c) == glue* c

  module _ {l} (left* : A → Type l) (right* : B → Type l)
    (glue* : (c : C) → left* (f c) ≃ right* (g c)) where

    private
      P = pushout-rec left* right* (ua ∘ glue*)

    abstract
      glue-path : (c : C) (a : left* (f c)) → coe (ap P (glue c)) a == –> (glue* c) a
      glue-path c a =
        coe (ap P (glue c)) a  =⟨ glue-β' left* right* (ua ∘ glue*) c |in-ctx (λ u → coe u a) ⟩
        coe (ua (glue* c)) a   =⟨ coe-β (glue* c) a ⟩
        –> (glue* c) a ∎
  
      !glue-path : (c : C) (b : right* (g c)) → coe! (ap P (glue c)) b == <– (glue* c) b
      !glue-path c b =
        coe! (ap P (glue c)) b  =⟨ glue-β' left* right* (ua ∘ glue*) c |in-ctx (λ u → coe! u b) ⟩
        coe! (ua (glue* c)) b   =⟨ coe!-β (glue* c) b ⟩
        <– (glue* c) b ∎

      ↓-glue-out : (c : C) {a : left* (f c)} {b : right* (g c)} → a == b [ P ↓ glue c ]
        → –> (glue* c) a == b
      ↓-glue-out c {a} {b} p =
        –> (glue* c) a =⟨ ! (glue-path c a) ⟩
        coe (ap P (glue c)) a =⟨ to-transp p ⟩
        b ∎

      ↓-glue-in : (c : C) {a : left* (f c)} {b : right* (g c)} → –> (glue* c) a == b
        → a == b [ P ↓ glue c ]
      ↓-glue-in c {a} {b} p = from-transp P (glue c) (glue-path c a ∙ p)

open Pushout public hiding (pushout)

pushout : ∀ {i j k} (d : Span i j k) → Type (max (max i j) k)
pushout d = Pushout.pushout {d = d}

_⊔^[_]_/_,_ : ∀ {i j k} (A : Type i) (C : Type k) (B : Type j)
  (f : C → A) (g : C → B) → Type (max (max i j) k)
A ⊔^[ C ] B  / f , g = pushout (span A B C f g)
