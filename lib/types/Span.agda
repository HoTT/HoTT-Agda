{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed

module lib.types.Span where

record Span {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
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
    (s : f == f' [ (λ CA → fst CA → snd CA) ↓ pair×= r p ])
    {g : C → B} {g' : C' → B'}
    (t : g == g' [ (λ CB → fst CB → snd CB) ↓ pair×= r q ])
    → (span A B C f g) == (span A' B' C' f' g')
  span=-raw idp idp idp idp idp = idp

abstract
  span= : ∀ {i j k} {A A' : Type i} (p : A ≃ A')
    {B B' : Type j} (q : B ≃ B') {C C' : Type k} (r : C ≃ C')
    {f : C → A} {f' : C' → A'} (s : (a : C) → (–> p) (f a) == f' (–> r a))
    {g : C → B} {g' : C' → B'} (t : (b : C) → (–> q) (g b) == g' (–> r b))
    → (span A B C f g) == (span A' B' C' f' g')
  span= p q r {f} {f'} s {g} {g'} t = span=-raw
    (ua p)
    (ua q)
    (ua r)
    (↓-→-in (λ α → ↓-snd×-in (ua r) (ua p) (↓-idf-ua-in p (
                   s _
                   ∙ ap f' (↓-idf-ua-out r (↓-fst×-out (ua r) (ua p) α))))))
    (↓-→-in (λ β → ↓-snd×-in (ua r) (ua q) (↓-idf-ua-in q (
                   t _
                   ∙ ap g' (↓-idf-ua-out r (↓-fst×-out (ua r) (ua q) β))))))

record Ptd-Span {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ptd-span
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : fst (Z ∙→ X)
    g : fst (Z ∙→ Y)

ptd-span-out : ∀ {i j k} → Ptd-Span {i} {j} {k} → Span {i} {j} {k}
ptd-span-out (ptd-span X Y Z f g) = span (fst X) (fst Y) (fst Z) (fst f) (fst g)

{- Helper for path induction on pointed spans -}
ptd-span-J : ∀ {i j k l} (P : Ptd-Span {i} {j} {k} → Type l)
  → ({A : Type i} {B : Type j} {Z : Ptd k} (f : fst Z → A) (g : fst Z → B)
     → P (ptd-span (A , f (snd Z)) (B , g (snd Z)) Z (f , idp) (g , idp)))
  → Π Ptd-Span P
ptd-span-J P t (ptd-span (A , ._) (B , ._) Z (f , idp) (g , idp)) = t f g
