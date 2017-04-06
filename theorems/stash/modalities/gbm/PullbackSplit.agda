{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.gbm.PullbackSplit where

--     L --> B    K = A ×_D C / (f,h)       d₁ = A -> D <- C
--     |     |g   L = B ×_A K / (g,left)    d₂ = B -> A <- K
--     v     v                              d  = B -> D <- C
--     K --> A
--     |     |f
--     v     v
--     C --> D
--        h

module PullbackLSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : A → D) (g : B → A) (h : C → D) where

  private
    d₁ : Cospan
    d₁ = cospan C A D h f

    d₂ : Cospan
    d₂ = cospan (Pullback d₁) B A Pullback.b g

    d : Cospan
    d = cospan C B D h (f ∘ g)

  split-equiv : Pullback d ≃ Pullback d₂
  split-equiv = equiv to from to-from from-to

    where to : Pullback d → Pullback d₂
          to (pullback c b p) = pullback (pullback c (g b) p) b idp

          from : Pullback d₂ → Pullback d
          from (pullback (pullback c a p) b idp) = pullback c b p

          to-from : (x : Pullback d₂) → to (from x) == x
          to-from (pullback _ b idp) = idp

          from-to : (x : Pullback d) → from (to x) == x
          from-to _ = idp
