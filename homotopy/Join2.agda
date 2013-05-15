{-# OPTIONS --without-K #-}

open import HoTT

-- Associativity of the join (work in progress)

module homotopy.Join2 where

  open import homotopy.Join

  apd= : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
         (p : (x : A) → f x == g x) {a b : A} (q : a == b)
         → apd f q ▹ p b == p a ◃ apd g q
  apd= {B = B} p {b} idp = idp▹ B (p b) ∙ ! (◃idp B (p b))

  apd=-red : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
             (p : (x : A) → f x == g x) {a b : A} (q : a == b)
             → apd f q == (p a ◃ apd g q) ▹! p b
  apd=-red {B = B} p {b} idp = {!!}

--   module Assoc2 {i j k} (A : Type i) (B : Type j) (C : Type k) where

--     open Assoc A B C

--     {- Here are the steps, without the junk around:

-- 1      apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))
-- 2      apd (λ x → ap to (from-glue (a , x))) (glue (b , c))
-- 3      apd (ap to) (apd (λ x → from-glue (a , x)) (glue (b , c)))
-- 4      apd (ap to) (from-glue-glue a (glue (b , c)))
-- 5      apd (ap to) (apd (λ x → glue (x , c)) (glue (a , b)))
-- 6      apd (λ x → ap to (glue (x , c))) (glue (a , b))
-- 7      apd (λ x → to-glue (x , c)) (glue (a , b))
-- 8      to-glue-glue c (a , b)
-- 9      apd (λ x → glue (a , x)) (glue (b , c))

--     -}
--     to-from-glue-glue' : (a : A) (bc : B × C)
--      → to-from-glue-left' a (fst bc) == to-from-glue-right' a (snd bc) [ (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x == to-from-left a ∙ glue (a , x)) ↓ glue bc ]
--     to-from-glue-glue' a (b , c) = ↓-=-in (!(
-- {- 1 -}
--       apd (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x) (glue (b , c)) ▹ to-from-glue-right' a c
--                  =⟨ stuff (λ x → ap to (ap from (glue (a , x)))) to-from-right (glue (b , c)) |in-ctx (λ u → u ▹ to-from-glue-right' a c) ⟩
--       ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (apd to-from-right (glue (b , c)))) ▹ to-from-glue-right' a c
--                  =⟨ glue-β to-from-right-left to-from-right-right to-from-right-glue (b , c) |in-ctx
--                            (λ u → ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 u) ▹ to-from-glue-right' a c) ⟩
--       ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c
--                  =⟨ {!!} ⟩
-- {- 2 -}
--       ((apd (λ x → ap to (from-glue (a , x))) (glue (b , c))) ∙'2 (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c
--                  =⟨ {!!} ⟩
-- {- 9 -}
--        to-from-glue-left' a b ◃ apd (λ x → glue (a , x)) (glue (b , c)) ∎))

--        -- ((↓-apd-out (λ a' _ → to (from (left a)) == to (from (right a'))) (λ x → glue (a , x)) (glue (b , c)) (apdd (ap to ∘ ap from) (glue (b , c)) (apd (λ x → (glue (a , x))) (glue (b , c))))) ∙'2 (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c =⟨ {!!} ⟩


--     -- to-from-glue-glue : (a : A) (bc : B × C)
--     --  → to-from-glue-left a (fst bc) == to-from-glue-right a (snd bc) [ (λ x → to-from-left a == to-from-right x [ (λ y → to (from y) == y) ↓ glue (a , x) ]) ↓ glue bc ]
--     -- to-from-glue-glue a (b , c) = {!!}  -- Should not be too hard

--     -- to-from-glue : (x : A × (B * C)) → to-from-left (fst x) == to-from-right (snd x) [ (λ x → to (from x) == x) ↓ glue x ]
--     -- to-from-glue (a , bc) = pushout-rec (to-from-glue-left a) (to-from-glue-right a) (to-from-glue-glue a) bc

--     -- to-from : (x : A * (B * C)) → to (from x) == x
--     -- to-from = pushout-rec to-from-left to-from-right to-from-glue

--   -- *-assoc : (A * B) * C ≃ A * (B * C)
--   -- *-assoc = equiv to from to-from from-to
