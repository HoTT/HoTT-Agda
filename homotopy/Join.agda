{-# OPTIONS --without-K #-}

open import HoTT

-- Associativity of the join (work in progress)

module homotopy.Join where

_*_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A * B = A ⊔^[ A × B ] B  / fst , snd

private
  module Assoc {i j k} (A : Type i) (B : Type j) (C : Type k) where

    {- First map -}

    to-left-left : A → A * (B * C)
    to-left-left a = left a

    to-left-right : B → A * (B * C)
    to-left-right b = right (left b)

    to-left-glue : (ab : A × B) → to-left-left (fst ab) == to-left-right (snd ab)
    to-left-glue (a , b) = glue (a , left b)

    to-left : A * B → A * (B * C)
    to-left = pushout-rec _ to-left-left to-left-right to-left-glue

    to-right : C → A * (B * C)
    to-right c = right (right c)

    to-glue-left : (c : C) (a : A) → to-left (left a) == to-right c
    to-glue-left c a = glue (a , right c)

    to-glue-right : (c : C) (b : B) → to-left (right b) == to-right c
    to-glue-right c b = ap right (glue (b , c))

    to-glue-glue : (c : C) (ab : A × B) → to-glue-left c (fst ab) == to-glue-right c (snd ab) [ (λ x → to-left x == to-right c) ↓ glue ab ]
    to-glue-glue c (a , b) = ↓-app='cst-in
      (glue (a , right c) =⟨ ! (↓-cst='app-out (apd (λ (x : B * C) → glue (a , x)) (glue (b , c)))) ⟩
       glue (a , left b) ∙' ap right (glue (b , c)) =⟨ ! (glue-β' _ to-left-left to-left-right to-left-glue (a , b)) |in-ctx (λ u → u ∙' ap right (glue (b , c))) ⟩
       ap to-left (glue (a , b)) ∙' ap right (glue (b , c)) ∎)

    to-glue : (ab-c : (A * B) × C) → to-left (fst ab-c) == to-right (snd ab-c)
    to-glue (ab , c) = pushout-elim _ (to-glue-left c) (to-glue-right c) (to-glue-glue c) ab

    to : (A * B) * C → A * (B * C)
    to = pushout-rec _ to-left to-right to-glue

    {- Second map -}

    from-left : A → (A * B) * C
    from-left a = left (left a)

    from-right-left : B → (A * B) * C
    from-right-left b = left (right b)

    from-right-right : C → (A * B) * C
    from-right-right c = right c

    from-right-glue : (bc : B × C) → from-right-left (fst bc) == from-right-right (snd bc)
    from-right-glue (b , c) = glue (right b , c)

    from-right : B * C → (A * B) * C
    from-right = pushout-rec _ from-right-left from-right-right from-right-glue

    from-glue-left : (a : A) (b : B) → from-left a == from-right (left b)
    from-glue-left a b = ap left (glue (a , b))

    from-glue-right : (a : A) (c : C) → from-left a == from-right (right c)
    from-glue-right a c = glue (left a , c)

    from-glue-glue : (a : A) (bc : B × C) → from-glue-left a (fst bc) == from-glue-right a (snd bc) [ (λ x → from-left a == from-right x) ↓ glue bc ]
    from-glue-glue a (b , c) = ↓-cst='app-in
      (ap left (glue (a , b)) ∙' ap from-right (glue (b , c)) =⟨ glue-β' _ from-right-left from-right-right from-right-glue (b , c) |in-ctx (λ u → ap left (glue (a , b)) ∙' u) ⟩
       ap left (glue (a , b)) ∙' glue (right b , c) =⟨ ! (↓-app='cst-out (apd (λ (x : A * B) → glue (x , c)) (glue (a , b)))) ⟩
       glue (left a , c) ∎)

    from-glue : (a-bc : A × (B * C)) → from-left (fst a-bc) == from-right (snd a-bc)
    from-glue (a , bc) = pushout-elim _ (from-glue-left a) (from-glue-right a) (from-glue-glue a) bc

    from : A * (B * C) → (A * B) * C
    from = pushout-rec _ from-left from-right from-glue

    {- First composite -}

    to-from-left : (a : A) → to (from (left a)) == left a
    to-from-left a = idp

    to-from-right-left : (b : B) → to (from (right (left b))) == right (left b)
    to-from-right-left b = idp
  
    to-from-right-right : (c : C) → to (from (right (right c))) == right (right c)
    to-from-right-right c = idp
  
    to-from-right-glue : (bc : B × C) → to-from-right-left (fst bc) == to-from-right-right (snd bc) [ (λ x → to (from (right x)) == right x) ↓ glue bc ]
    to-from-right-glue (b , c) = ↓-='-in (!
                    (ap (λ z → to (from (right z))) (glue (b , c)) =⟨ idp ⟩
                     ap (λ z → to (from-right z)) (glue (b , c)) =⟨ ap-∘ to from-right (glue (b , c)) ⟩
                     ap to (ap from-right (glue (b , c))) =⟨ glue-β' _ from-right-left from-right-right from-right-glue (b , c) |in-ctx ap to ⟩
                     ap to (glue ((right b , c) :> (A * B) × C)) =⟨ glue-β' (A * (B * C)) to-left to-right to-glue ((right b , c) :> (A * B) × C) ⟩
                     to-glue ((right b , c) :> (A * B) × C) =⟨ idp ⟩
                     ap right (glue (b , c)) ∎))

    to-from-right : (bc : B * C) → to (from (right bc)) == right bc
    to-from-right = pushout-elim _ to-from-right-left to-from-right-right to-from-right-glue

    to-from-glue-left' : (a : A) (b : B) → ap to (ap from (glue (a , left b))) == glue (a , left b)
    to-from-glue-left' a b =
      (ap to (ap from (glue (a , left b))) =⟨ glue-β' _ from-left from-right from-glue (a , left b) |in-ctx ap to ⟩
       ap to (from-glue (a , left b)) =⟨ idp ⟩
       ap to (ap left (glue (a , b))) =⟨ ∘-ap to left (glue (a , b)) ⟩
       ap (to ∘ left) (glue (a , b)) =⟨ idp ⟩
       ap to-left (glue (a , b)) =⟨ glue-β' _ to-left-left to-left-right to-left-glue (a , b) ⟩
       to-left-glue (a , b) =⟨ idp ⟩
       glue (a , left b) ∎)

    to-from-glue-left : (a : A) (b : B) → to-from-left a == to-from-right (left b) [ (λ x → to (from x) == x) ↓ glue (a , left b) ]
    to-from-glue-left a b = ↓-∘=id-in from to (to-from-glue-left' a b)

    to-from-glue-right' : (a : A) (c : C) → ap to (ap from (glue (a , right c))) == glue (a , right c)
    to-from-glue-right' a c =
      (ap to (ap from (glue (a , right c))) =⟨ glue-β' _ from-left from-right from-glue (a , right c) |in-ctx ap to ⟩
       ap to (from-glue (a , right c)) =⟨ idp ⟩
       ap to (glue (left a , c)) =⟨ glue-β' _ to-left to-right to-glue (left a , c) ⟩
       to-glue (left a , c) =⟨ idp ⟩
       glue (a , right c) ∎)

    to-from-glue-right : (a : A) (c : C) → to-from-left a == to-from-right (right c) [ (λ x → to (from x) == x) ↓ glue (a , right c) ]
    to-from-glue-right a c = ↓-∘=id-in from to (to-from-glue-right' a c)

    to-from-glue-glue' : (a : A) (bc : B × C)
     → to-from-glue-left' a (fst bc) == to-from-glue-right' a (snd bc) [ (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x == to-from-left a ∙ glue (a , x)) ↓ glue bc ]
    to-from-glue-glue' a (b , c) = ↓-=-in (!
      (apd (λ x → ap to (ap from (glue (a , x))) ∙' to-from-right x) (glue (b , c)) ▹ to-from-glue-right' a c =⟨ {!!} ⟩
       ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (apd to-from-right (glue (b , c)))) ▹ to-from-glue-right' a c =⟨ {!!} ⟩
       ((apd (λ x → ap to (ap from (glue (a , x)))) (glue (b , c))) ∙'2 (to-from-right-glue (b , c))) ▹ to-from-glue-right' a c =⟨ {!!} ⟩
       to-from-glue-left' a b ◃ apd (λ x → glue (a , x)) (glue (b , c)) ∎))

    -- to-from-glue-glue : (a : A) (bc : B × C)
    --  → to-from-glue-left a (fst bc) == to-from-glue-right a (snd bc) [ (λ x → to-from-left a == to-from-right x [ (λ y → to (from y) == y) ↓ glue (a , x) ]) ↓ glue bc ]
    -- to-from-glue-glue a (b , c) = {!!}  -- Should not be too hard

    -- to-from-glue : (x : A × (B * C)) → to-from-left (fst x) == to-from-right (snd x) [ (λ x → to (from x) == x) ↓ glue x ]
    -- to-from-glue (a , bc) = pushout-rec _ (to-from-glue-left a) (to-from-glue-right a) (to-from-glue-glue a) bc

    -- to-from : (x : A * (B * C)) → to (from x) == x
    -- to-from = pushout-rec _ to-from-left to-from-right to-from-glue

  -- *-assoc : (A * B) * C ≃ A * (B * C)
  -- *-assoc = equiv to from to-from from-to
