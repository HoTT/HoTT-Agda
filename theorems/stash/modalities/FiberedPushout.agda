{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.FiberedPushout {i j k} {X : Type i} {Y : Type j} where

  {-
     X ---glue-left--- P ---glue-right--- Y
  -}

  module _ (P : X → Y → Type k) where
    fibered-pushout-span : Span
    fibered-pushout-span = record
      { A = Σ X λ x → Σ Y λ y → P x y
      ; B = Coprod X Y
      ; C = Coprod (Σ X λ x → Σ Y λ y → P x y) (Σ X λ x → Σ Y λ y → P x y)
      ; f = λ{ (inl p) → p ; (inr p) → p}
      ; g = λ{ (inl p) → inl (fst p) ; (inr p) → inr (fst (snd p))}
      }

    FiberedPushout : Type (lmax (lmax i j) k)
    FiberedPushout = Pushout fibered-pushout-span

  module _ {P : X → Y → Type k} where
    in-left : X → FiberedPushout P
    in-left = right ∘ inl

    in-right : Y → FiberedPushout P
    in-right = right ∘ inr

    in-mid : ∀ {x y} → P x y → FiberedPushout P
    in-mid p = left (_ , _ , p)

    glue-left : ∀ {x y} (p : P x y) → in-mid p == in-left x
    glue-left p = glue (inl (_ , _ , p))

    glue-right : ∀ {x y} (p : P x y) → in-mid p == in-right y
    glue-right p = glue (inr (_ , _ , p))

    module FiberedPushoutElim {l}
      (C : FiberedPushout P → Type l)
      (b1 : (x : X) → C (in-left x))
      (b2 : (x : X) (y : Y) (p : P x y) → C (in-mid p))
      (b3 : (y : Y) → C (in-right y))
      (glue-left' : (x : X) (y : Y) (p : P x y) → b2 x y p == b1 x [ C ↓ glue-left p ])
      (glue-right' : (x : X) (y : Y) (p : P x y) → b2 x y p == b3 y [ C ↓ glue-right p ])
      where

      private
        module PElim = PushoutElim {d = fibered-pushout-span P} {P = C}
          (λ{(x , y , p) → b2 x y p})
          (λ{(inl x) → b1 x ; (inr y) → b3 y})
          (λ{(inl (_ , _ , p)) → glue-left'  _ _ p
           ; (inr (_ , _ , p)) → glue-right' _ _ p})

      f = PElim.f

      glue-left-β : ∀ {x y} (p : P x y) → apd f (glue-left p) == glue-left' x y p
      glue-left-β p = PElim.glue-β (inl (_ , _ , p))

      glue-right-β : ∀ {x y} (p : P x y) → apd f (glue-right p) == glue-right' x y p
      glue-right-β p = PElim.glue-β (inr (_ , _ , p))
