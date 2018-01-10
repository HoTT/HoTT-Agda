{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- XXX this file should be moved to a better place. -}

module homotopy.freudenthal.TruncationLadder where

  up : ∀ {i} {X : Ptd i} → de⊙ X → north' (de⊙ X) == north
  up {X = X} x = merid x ∙ ! (merid (pt X))

  ⊙up : ∀ {i} (X : Ptd i) → X ⊙→ ⊙Ω (⊙Susp X)
  ⊙up X = up , !-inv-r (merid (pt X))

  ⊙Ω-Trunc : ∀ {i} {n : ℕ₋₂} (X : Ptd i)
    → ⊙Ω (⊙Trunc (S n) X) ⊙≃ ⊙Trunc n (⊙Ω X)
  ⊙Ω-Trunc X = ≃-to-⊙≃ (Trunc=-equiv [ pt X ] [ pt X ]) idp

  step'' : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) n
    → ⊙CommSquare
        (⊙Ω-fmap (⊙Trunc-fmap f)) (⊙Trunc-fmap (⊙Ω-fmap f))
        (⊙–> (⊙Ω-Trunc X))
        (⊙–> (⊙Ω-Trunc {n = n} Y))
  step'' (f , idp) n = ⊙comm-sqr (Trunc=-equiv-nat _ _ _ , idp)

  step' : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) m n
    → ⊙CommSquare
        (⊙Ω^'-fmap (S m) (⊙Trunc-fmap f)) (⊙Ω^'-fmap m (⊙Trunc-fmap (⊙Ω-fmap f)))
        (⊙–> (⊙Ω^'-emap m (⊙Ω-Trunc X)))
        (⊙–> (⊙Ω^'-emap m (⊙Ω-Trunc {n = n} Y)))
  step' f m n = ⊙Ω^'-csmap m (step'' f n)

  step : ∀ {i} (X : Ptd i) m n
    → ⊙CommSquare
        (⊙Ω^'-fmap (S m) (⊙Trunc-fmap (⊙Ω^-fmap n (⊙up X))))
        (⊙Ω^'-fmap m (⊙Trunc-fmap (⊙Ω^-fmap (S n) (⊙up X))))
        (⊙–> (⊙Ω^'-emap m (⊙Ω-Trunc (⊙Ω^ n X))))
        (⊙–> (⊙Ω^'-emap m (⊙Ω-Trunc {n = ⟨ m ⟩} (⊙Ω^ n (⊙Ω (⊙Susp X))))))
  step X m n = step' (⊙Ω^-fmap n (⊙up X)) m ⟨ m ⟩

  rail : ∀ {i} (X : Ptd i) m n
    → ⊙Ω^' m (⊙Trunc ⟨ m ⟩ (⊙Ω^ n X)) ⊙≃ ⊙Trunc 0 (⊙Ω^' m (⊙Ω^ n X))
  rail X O _ = ⊙ide _
  rail X (S m) n = rail X m (S n) ⊙∘e ⊙Ω^'-emap m (⊙Ω-Trunc (⊙Ω^ n X))

  ladder' : ∀ {i} (X : Ptd i) m n
    → ⊙CommSquare
        (⊙Ω^'-fmap m (⊙Trunc-fmap (⊙Ω^-fmap n (⊙up X))))
        (⊙Trunc-fmap (⊙Ω^'-fmap m (⊙Ω^-fmap n (⊙up X))))
        (⊙–> (rail X m n))
        (⊙–> (rail (⊙Ω (⊙Susp X)) m n))
  ladder' X O _ = ⊙comm-sqr (⊙∘-unit-l _)
  ladder' X (S m) n =
    ⊙CommSquare-∘v (ladder' X m (S n)) (step X m n)

  ladder : ∀ {i} (X : Ptd i) m
    → ⊙CommSquare
        (⊙Ω^'-fmap m (⊙Trunc-fmap (⊙up X)))
        (⊙Trunc-fmap (⊙Ω^'-fmap m (⊙up X)))
        (⊙–> (rail X m 0))
        (⊙–> (rail (⊙Ω (⊙Susp X)) m 0))
  ladder X m = ladder' X m 0
