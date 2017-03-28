{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module FiberedPushout where

  module _ {ℓ} {X Y : Type ℓ} where

    private

      data #FiberedPushout (P : X → Y → Type ℓ) : Type ℓ where
        #in-left : X → #FiberedPushout P
        #in-mid : {x : X} {y : Y} → P x y → #FiberedPushout P
        #in-right : Y → #FiberedPushout P

    FiberedPushout : (P : X → Y → Type ℓ) → Type ℓ
    FiberedPushout = #FiberedPushout

    in-left : {P : X → Y → Type ℓ} → X → FiberedPushout P
    in-left = #in-left

    in-right : {P : X → Y → Type ℓ} → Y → FiberedPushout P
    in-right = #in-right

    in-mid : {P : X → Y → Type ℓ} {x : X} {y : Y} → P x y → FiberedPushout P
    in-mid = #in-mid

    postulate
      glue-left : {P : X → Y → Type ℓ} {x : X} {y : Y} → (p : P x y) → in-mid {P} p == in-left x
      glue-right : {P : X → Y → Type ℓ} {x : X} {y : Y} → (p : P x y) → in-mid {P} p == in-right y

    module FiberedPushoutElim {P : X → Y → Type ℓ} {κ}
             (C : FiberedPushout P → Type κ)
             (b1 : (x : X) → C (in-left x))
             (b2 : (x : X) (y : Y) (p : P x y) → C (in-mid p))
             (b3 : (y : Y) → C (in-right y))
             (glue-left' : (x : X) (y : Y) (p : P x y) → b2 x y p == b1 x [ C ↓ glue-left p ])
             (glue-right' : (x : X) (y : Y) (p : P x y) → b2 x y p == b3 y [ C ↓ glue-right p ])
             where

      f : Π (FiberedPushout P) C
      f (#in-left x) = b1 x
      f (#in-mid p) = b2 _ _ p
      f (#in-right y) = b3 y

    -- Todo : HIT β-rules
    
--       postulate {- HoTT Axiom -}
--         Pushout-elim/βgluel : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
--                               (b1 : (x : X) → C (inl x))
--                               (b2 : (x : X) (y : Y) (p : P x y) → C (inm p))
--                               (b3 : (y : Y) → C (inr y))
--                               (gluel' : (x : X) (y : Y) (p : P x y) → PathOver C (gluel p) (b2 x y p) (b1 x))
--                               (gluer' : (x : X) (y : Y) (p : P x y) → PathOver C (gluer p) (b2 x y p) (b3 y))
--                               (x : X) → (y : Y) → (p : P x y) → 
--                               Path (apdo (Pushout-elim C b1 b2 b3 gluel' gluer') (gluel p))
--                                    (gluel' x y p)

--         Pushout-elim/βgluer : {X Y : Type} {P : X → Y → Type} (C : Pushout P → Type)
--                               (b1 : (x : X) → C (inl x))
--                               (b2 : (x : X) (y : Y) (p : P x y) → C (inm p))
--                               (b3 : (y : Y) → C (inr y))
--                               (gluel' : (x : X) (y : Y) (p : P x y) → PathOver C (gluel p) (b2 x y p) (b1 x))
--                               (gluer' : (x : X) (y : Y) (p : P x y) → PathOver C (gluer p) (b2 x y p) (b3 y))
--                               (x : X) → (y : Y) → (p : P x y) → 
--                               Path (apdo (Pushout-elim C b1 b2 b3 gluel' gluer') (gluer p))
--                                    (gluer' x y p)
