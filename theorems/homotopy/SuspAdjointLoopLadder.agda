{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdAdjoint

module homotopy.SuspAdjointLoopLadder where

  import homotopy.SuspAdjointLoop as A

  step : ∀ {i} {X Y Z : Ptd i} (f : Y ⊙→ Z)
    → CommSquareEquiv
        ((f ⊙∘_) :> ((⊙Susp (de⊙ X) ⊙→ Y) → (⊙Susp (de⊙ X) ⊙→ Z)))
        (⊙Ω-fmap f ⊙∘_)
        (–> (A.eq X Y))
        (–> (A.eq X Z))
  step f = comm-sqr (! ∘ A.nat-cod _ f) ,
    snd (A.eq _ _) , snd (A.eq _ _)

  rail : ∀ {i} {X Y : Ptd i} n
    → (⊙Susp^ n X ⊙→ Y) → (X ⊙→ ⊙Ω^' n Y)
  rail O = idf _
  rail (S n) = rail n ∘ –> (A.eq _ _)

  ladder : ∀ {i} {X Y Z : Ptd i} n (f : Y ⊙→ Z)
    → CommSquareEquiv
        ((f ⊙∘_) :> ((⊙Susp^ n X ⊙→ Y) → (⊙Susp^ n X ⊙→ Z)))
        (⊙Ω^'-fmap n f ⊙∘_)
        (rail n)
        (rail n)
  ladder O _ = (comm-sqr λ _ → idp) , idf-is-equiv _ , idf-is-equiv _
  ladder (S n) f = CommSquareEquiv-∘v (ladder n (⊙Ω-fmap f)) (step f)
