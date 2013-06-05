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
           {u : B b} (s : g b =-= u)
           → apd f q ▹ (↯ _ =⟪ p b ⟫ s) == p a ◃ (apd g q ▹ (↯ s))
apd=-red {B = B} p {b} idp s = {!!}

module Assoc2 {i j k} (A : Type i) (B : Type j) (C : Type k) where

  open Assoc A B C

  {- Here are the steps, without the junk around:

1      apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))
2      apd (λ x → ap to (from-glue (a , x))) (glue (b , c))
3      apd (λ x → ap to {x = from-left a} {y = from-right x}) (glue (b , c)) (from-glue-glue a (b , c))
4      apd (λ x → ap to {x = from-left a} {y = from-right x}) (glue (b , c)) (apd (λ x → glue (x , c)) (glue (a , b)))
5      apd (λ x → ap to (glue (x , c))) (glue (a , b))
6      apd (λ x → to-glue (x , c)) (glue (a , b))
7      to-glue-glue c (a , b)
=      apd (λ x → glue (a , x)) (glue (b , c))

  -}

  to-from-glue-glue' : (a : A) (b : B) (c : C)
   → (↯ to-from-glue-left' a b) == (↯ to-from-glue-right' a c) [ (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x == glue (a , x)) ↓ glue (b , c) ]
  to-from-glue-glue' a b c = ↓-=-in (!(
{- 1 -}
    apd (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)
               =⟨ stuff (λ x → ap to (ap from (glue (a , x)))) to-from-right (glue (b , c)) |in-ctx (λ u → u ▹ (↯ to-from-glue-right' a c)) ⟩
    ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (apd to-from-right (glue (b , c)))) ▹ (↯ to-from-glue-right' a c)
               =⟨ ToFromRight.glue-β (b , c) |in-ctx
                         (λ u → ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 u) ▹ (↯ to-from-glue-right' a c)) ⟩
    ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (to-from-right-glue (b , c))) ▹ (↯ to-from-glue-right' a c)
               =⟨ {!!} ⟩
    (apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)) ∙'2 (to-from-right-glue (b , c))
               =⟨ apd=-red (λ x → ap (ap to) (From.glue-β (a , x))) (glue (b , c)) _ |in-ctx (λ u → u ∙'2 (to-from-right-glue (b , c))) ⟩
    ((↯ 1# (to-from-glue-left' a b)) ◃ (apd (λ x → ap to (from-glue (a , x))) (glue (b , c)) ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2 (to-from-right-glue (b , c))
               =⟨ {!!} ⟩
    ((↯ 1# (to-from-glue-left' a b)) ◃ ((api2 (λ x → ap to) (apd (λ x → from-glue (a , x)) (glue (b , c)))) ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2 (to-from-right-glue (b , c))
               =⟨ {!!} ⟩

{- 2 -}
    -- (↯ 1# (to-from-glue-left' a b)) ◃ ((apd (λ x → ap to (from-glue (a , x)) ∙' to-from-right x) (glue (b , c))) ▹ (↯ 1! (to-from-glue-right' a c)))
    --            =⟨ ? ⟩
    --            =⟨ {!!} ⟩
-- {- 3 -}
--     (↯ 1# (to-from-glue-left' a b)) ◃ (((↓-→-out (apd (λ x → ap to) (glue (b , c))) (from-glue-glue a (b , c))) ∙'2 (to-from-right-glue (b , c))) ▹ (↯ 1! (to-from-glue-right' a c)))
--                =⟨ {!!} ⟩
-- {- 4 -}
-- {- 5 -}
--      (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (To.glue-β (left a , c) !◃ (apd (λ x → ap to (glue (x , c))) (glue (a , b)) ▹ To.glue-β (right b , c))))
--                =⟨ {!!} ⟩
-- {- 6 -}
--      (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (apd (λ x → to-glue (x , c)) (glue (a , b))))
--                =⟨ {!!} ⟩
-- {- 7 -}
--      (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (to-glue-glue c (a , b)))
--                =⟨ {!!} ⟩
     (↯ to-from-glue-left' a b) ◃ apd (λ x → glue (a , x)) (glue (b , c)) ∎))

       -- ((↓-apd-out (λ a' _ → to (from (left a)) == to (from (right a'))) (λ x → glue (a , x)) (glue (b , c)) (apdd (ap to ∘ ap from) (glue (b , c)) (apd (λ x → (glue (a , x))) (glue (b , c))))) ∙'2 (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c =⟨ {!!} ⟩


    -- to-from-glue-glue : (a : A) (bc : B × C)
    --  → to-from-glue-left a (fst bc) == to-from-glue-right a (snd bc) [ (λ x → to-from-left a == to-from-right x [ (λ y → to (from y) == y) ↓ glue (a , x) ]) ↓ glue bc ]
    -- to-from-glue-glue a (b , c) = {!!}  -- Should not be too hard

    -- to-from-glue : (x : A × (B * C)) → to-from-left (fst x) == to-from-right (snd x) [ (λ x → to (from x) == x) ↓ glue x ]
    -- to-from-glue (a , bc) = pushout-rec (to-from-glue-left a) (to-from-glue-right a) (to-from-glue-glue a) bc

    -- to-from : (x : A * (B * C)) → to (from x) == x
    -- to-from = pushout-rec to-from-left to-from-right to-from-glue

  -- *-assoc : (A * B) * C ≃ A * (B * C)
  -- *-assoc = equiv to from to-from from-to
