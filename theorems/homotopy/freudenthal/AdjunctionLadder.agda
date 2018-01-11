{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- XXX this file should be moved to a better place. -}

module homotopy.freudenthal.AdjunctionLadder where

  up : ∀ {i} {X : Ptd i} → de⊙ X → north' (de⊙ X) == north
  up {X = X} x = merid x ∙ ! (merid (pt X))

  ⊙up : ∀ {i} (X : Ptd i) → X ⊙→ ⊙Ω (⊙Susp X)
  ⊙up X = up , !-inv-r (merid (pt X))

  rail : ∀ {i j} {X : Ptd i} {Y : Ptd j} n
    → (⊙Susp^ n X ⊙→ Y) → (X ⊙→ ⊙Ω^' n Y)
  rail O f = f
  rail (S n) f = rail n (⊙Ω-fmap f ⊙∘ ⊙up _)

  rail-∘ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
    → (n : ℕ) (g : Y ⊙→ Z) (f : ⊙Susp^ n X ⊙→ Y)
    → rail n (g ⊙∘ f) == ⊙Ω^'-fmap n g ⊙∘ rail n f
  rail-∘ O _ _ = idp
  rail-∘ (S n) g f =
    rail n (⊙Ω-fmap (g ⊙∘ f) ⊙∘ ⊙up _)
      =⟨ ap (λ f → rail n (f ⊙∘ ⊙up _)) (⊙Ω-fmap-∘ g f) ⟩
    rail n ((⊙Ω-fmap g ⊙∘ ⊙Ω-fmap f) ⊙∘ ⊙up _)
      =⟨ ap (rail n) $ ⊙λ= $ ⊙∘-assoc (⊙Ω-fmap g) (⊙Ω-fmap f) (⊙up _) ⟩
    rail n (⊙Ω-fmap g ⊙∘ (⊙Ω-fmap f ⊙∘ ⊙up _))
      =⟨ rail-∘ n (⊙Ω-fmap g) (⊙Ω-fmap f ⊙∘ ⊙up _) ⟩
    ⊙Ω^'-fmap (S n) g ⊙∘ rail n (⊙Ω-fmap f ⊙∘ ⊙up _)
      =∎

  ladder : ∀ {i j} {X : Ptd i} {Y : Ptd j} n
    → CommSquare
        ((⊙up Y ⊙∘_) :> ((⊙Susp^ n X ⊙→ Y) → (⊙Susp^ n X ⊙→ ⊙Ω (⊙Susp Y))))
        (⊙Ω^'-fmap n (⊙up Y) ⊙∘_)
        (rail n) (rail n)
  ladder n = comm-sqr $ rail-∘ n (⊙up _)
