{-# OPTIONS --without-K #-}

open import HoTT

-- Associativity of the join (work in progress)

module experimental.JoinAssoc2 where

import experimental.JoinAssoc as Assoc

module Assoc2 {i j k} (A : Type i) (B : Type j) (C : Type k) where

  open Assoc A B C

  {- Here are the steps, without the junk around:

       apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))
1 (From.glue-β)
       apd (λ x → ap to (from-glue (a , x))) (glue (b , c))
2 (unfuse)
       ap↓ (λ x → ap to {x = from-left a} {y = from-right x}) (apd (λ x → from-glue (a , x)) (glue (b , c)))
3 (FromGlue.glue-β)
       ap↓ (λ x → ap to {x = from-left a} {y = from-right x}) (apd (λ x → glue (x , c)) (glue (a , b)))
4 (fuse)
       apd (λ x → ap to (glue (x , c))) (glue (a , b))
5 (To.glue-β)
       apd (λ x → to-glue (x , c)) (glue (a , b))
6 (ToGlue.glue-β)
       apd (λ x → glue (a , x)) (glue (b , c))

  -}

  to-from-glue-glue' : (a : A) (b : B) (c : C)
   → (↯ to-from-glue-left' a b) == (↯ to-from-glue-right' a c) [ (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x == glue (a , x)) ↓ glue (b , c) ]
  to-from-glue-glue' a b c =
    ↓-=-in (!(
    apd (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)
               =⟨ apd∙' (λ x → ap to (ap from (glue (a , x)))) to-from-right (glue (b , c)) |in-ctx (λ u → u ▹ (↯ to-from-glue-right' a c)) ⟩
    ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2ᵈ (apd to-from-right (glue (b , c)))) ▹ (↯ to-from-glue-right' a c)
               =⟨ ToFromRight.glue-β (b , c) |in-ctx
                         (λ u → ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2ᵈ u) ▹ (↯ to-from-glue-right' a c)) ⟩
    ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2ᵈ (to-from-right-glue (b , c))) ▹ (↯ to-from-glue-right' a c)
               =⟨ ▹-∙'2ᵈ (apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) (to-from-right-glue (b , c)) (↯ to-from-glue-right' a c) idp ⟩
    (apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)) ∙'2ᵈ (to-from-right-glue (b , c) ▹ idp)
               =⟨ (▹idp (to-from-right-glue (b , c))) |in-ctx (λ u → (apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)) ∙'2ᵈ u) ⟩
    (apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c)) ▹ (↯ to-from-glue-right' a c)) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ apd=-red (λ x → ap (ap to) (From.glue-β (a , x))) (glue (b , c)) (1! (to-from-glue-right' a c)) |in-ctx (λ u → u ∙'2ᵈ (to-from-right-glue (b , c))) ⟩
{- 1 -}
    ((↯ 1# (to-from-glue-left' a b)) ◃ (apd (λ x → ap to (from-glue (a , x))) (glue (b , c)) ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ apd-∘' (ap to) (λ x → from-glue (a , x)) (glue (b , c)) |in-ctx (λ u → ((↯ 1# (to-from-glue-left' a b)) ◃ (u ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩
{- 2 -}
    ((↯ 1# (to-from-glue-left' a b)) ◃ (ap↓ (ap to) (apd (λ x → from-glue (a , x)) (glue (b , c))) ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ FromGlue.glue-β a (b , c) |in-ctx (λ u → ((↯ 1# (to-from-glue-left' a b)) ◃ (ap↓ (ap to) u ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩
{- 3 -}
    ((↯ 1# (to-from-glue-left' a b)) ◃ (ap↓ (ap to) (from-glue-glue a (b , c)) ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ idp ⟩

    ((↯ 1# (to-from-glue-left' a b)) ◃ (ap↓ (ap to) (↓-swap! left from-right _ idp
      (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ Ap↓-swap!.β to left from-right _ idp (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c)))
                  |in-ctx (λ u → ((↯ 1# (to-from-glue-left' a b)) ◃ (u ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩

    ((↯ 1# (to-from-glue-left' a b)) ◃ (((ap (λ u → u) (∘-ap to left (glue (a , b)))) ◃ ↓-swap! (to ∘ left) (to ∘ from-right) _ idp (ap↓ (ap to) (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ ap-idf (∘-ap to left (glue (a , b))) |in-ctx (λ v → ((↯ 1# (to-from-glue-left' a b)) ◃ ((v ◃ ↓-swap! (to ∘ left) (to ∘ from-right) _ idp (ap↓ (ap to) (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩

    ((↯ 1# (to-from-glue-left' a b)) ◃ (((∘-ap to left (glue (a , b))) ◃ ↓-swap! (to ∘ left) (to ∘ from-right) _ idp (ap↓ (ap to) (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ {!!} ⟩

    ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp (ap↓ (ap to) (apd (λ x → glue (x , c)) (glue (a , b)) ▹! (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ ap↓-▹! (ap to) (apd (λ x → glue (x , c)) (glue (a , b))) (FromRight.glue-β (b , c)) |in-ctx (λ v → ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp (v ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩

    ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp ((ap↓ (ap to) (apd (λ x → glue (x , c)) (glue (a , b))) ▹! ap (ap to) (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ ∘'-apd (ap to) (λ x → glue (x , c)) (glue (a , b)) |in-ctx (λ v → ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp ((v ▹! ap (ap to) (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))) ⟩
{- 4 -}

    ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp ((apd (λ x → ap to (glue (x , c))) (glue (a , b)) ▹! ap (ap to) (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
               =⟨ {!!} ⟩
{- 5 -}

    -- ((↯ 2# (to-from-glue-left' a b)) ◃ ((↓-swap! to-left (to ∘ from-right) _ idp ((apd (λ x → to-glue (x , c)) (glue (a , b)) ▹! ap (ap to) (FromRight.glue-β (b , c))) ▹ (ap (λ u → u) (∘-ap to from-right (glue (b , c))))))
    -- ▹ (↯ 1! (to-from-glue-right' a c)))) ∙'2ᵈ (to-from-right-glue (b , c))
    --            =⟨ {!!} ⟩

-- {- 5 -}
--      (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (To.glue-β (left a , c) !◃ (apd (λ x → ap to (glue (x , c))) (glue (a , b)) ▹ To.glue-β (right b , c))))
--                =⟨ {!!} ⟩
     (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (apd (λ x → to-glue (x , c)) (glue (a , b))))
               =⟨ ToGlue.glue-β c (a , b) |in-ctx (λ v → (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp v)) ⟩
{- 6 -}

     (↯ 2# (to-from-glue-left' a b)) ◃ (↓-swap! to-left right _ idp (to-glue-glue c (a , b)))
               =⟨ ↓-swap-β to-left right {p = glue (a , b)} (to-glue-left c a) idp (ToLeft.glue-β (a , b) ◃ apd (λ x → glue (a , x)) (glue (b , c))) |in-ctx (λ v → (↯ 2# (to-from-glue-left' a b)) ◃ v) ⟩
     (↯ 2# (to-from-glue-left' a b)) ◃ (ToLeft.glue-β (a , b) ◃ apd (λ x → glue (a , x)) (glue (b , c)))
               =⟨ {!!} ⟩ -- associativity
     (↯ to-from-glue-left' a b) ◃ apd (λ x → glue (a , x)) (glue (b , c)) ∎))

       -- ((↓-apd-out (λ a' _ → to (from (left a)) == to (from (right a'))) (λ x → glue (a , x)) (glue (b , c)) (apdd (ap to ∘ ap from) (glue (b , c)) (apd (λ x → (glue (a , x))) (glue (b , c))))) ∙'2ᵈ (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c =⟨ {!!} ⟩


    -- to-from-glue-glue : (a : A) (bc : B × C)
    --  → to-from-glue-left a (fst bc) == to-from-glue-right a (snd bc) [ (λ x → to-from-left a == to-from-right x [ (λ y → to (from y) == y) ↓ glue (a , x) ]) ↓ glue bc ]
    -- to-from-glue-glue a (b , c) = {!!}  -- Should not be too hard

    -- to-from-glue : (x : A × (B * C)) → to-from-left (fst x) == to-from-right (snd x) [ (λ x → to (from x) == x) ↓ glue x ]
    -- to-from-glue (a , bc) = pushout-rec (to-from-glue-left a) (to-from-glue-right a) (to-from-glue-glue a) bc

    -- to-from : (x : A * (B * C)) → to (from x) == x
    -- to-from = pushout-rec to-from-left to-from-right to-from-glue

  -- *-assoc : (A * B) * C ≃ A * (B * C)
  -- *-assoc = equiv to from to-from from-to
