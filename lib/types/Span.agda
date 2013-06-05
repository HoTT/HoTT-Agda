{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi

module lib.types.Span where

record Span (i j k : ULevel) : Type (suc (max (max i j) k)) where
  constructor span
  field
    A : Type i
    B : Type j
    C : Type k
    g : C → A
    h : C → B

private
  span=-raw : ∀ {i j k} {A A' : Type i} (p : A == A')
    {B B' : Type j} (q : B == B') {C C' : Type k} (r : C == C')
    {g : C → A} {g' : C' → A'}
    (s : g == g' [ (λ CA → fst CA → snd CA) ↓ pair=' r p ])
    {h : C → B} {h' : C' → B'}
    (t : h == h' [ (λ CB → fst CB → snd CB) ↓ pair=' r q ])
    → (span A B C g h) == (span A' B' C' g' h')
  span=-raw idp idp idp idp idp = idp

abstract
  span= : ∀ {i j k} {A A' : Type i} (p : A ≃ A')
    {B B' : Type j} (q : B ≃ B') {C C' : Type k} (r : C ≃ C')
    {g : C → A} {g' : C' → A'} (s : (a : C) → (–> p) (g a) == g' (–> r a))
    {h : C → B} {h' : C' → B'} (t : (b : C) → (–> q) (h b) == h' (–> r b))
    → (span A B C g h) == (span A' B' C' g' h')
  span= p q r {g} {g'} s {h} {h'} t = span=-raw
    (ua p)
    (ua q)
    (ua r)
    (↓-→-in (λ α → ↓-snd-in (ua r) (ua p) (↓-idf-ua-in p (
                   s _
                   ∙ ap g' (↓-idf-ua-out r (↓-fst-out (ua r) (ua p) α))))))
    (↓-→-in (λ β → ↓-snd-in (ua r) (ua q) (↓-idf-ua-in q (
                   t _
                   ∙ ap h' (↓-idf-ua-out r (↓-fst-out (ua r) (ua q) β))))))
