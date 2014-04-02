{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory

open import lib.types.Interval

module cohomology.Sn (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT


C-Sphere-below : (n : ℕ) (m : ℕ) → (n < m) 
  → C n (Ptd-Sphere m) == LiftUnit-Group
C-Sphere-below O .1 ltS = contr-iso-LiftUnit _ $ C-SuspO (Ptd-Sphere 0)
C-Sphere-below O (S m) (ltSR _) = contr-iso-LiftUnit _ $ C-SuspO (Ptd-Sphere m)
C-Sphere-below (S n) .(S (S n)) ltS = 
  C-SuspS n (Ptd-Sphere (S n)) ∙ C-Sphere-below n (S n) ltS
C-Sphere-below (S n) (S m) (ltSR lt) = 
  C-SuspS n (Ptd-Sphere m) ∙ C-Sphere-below n m (<-cancel-S (ltSR lt))


C-Sphere-diag : (n : ℕ) → C n (Ptd-Sphere n) == C 0 Ptd-Bool
C-Sphere-diag O = idp
C-Sphere-diag (S n) = C-SuspS n (Ptd-Sphere n) ∙ C-Sphere-diag n


C-Sphere-above : (n : ℕ) (m : ℕ) → (m < n)
  → C n (Ptd-Sphere m) == LiftUnit-Group
C-Sphere-above .1 O ltS = contr-iso-LiftUnit _ $ 
  transport (λ A → is-contr (CEl 1 A)) 
            (ptd-ua lift-equiv idp) (C-dimensionS 0)
C-Sphere-above (S n) O (ltSR _) = contr-iso-LiftUnit _ $ 
  transport (λ A → is-contr (CEl (S n) A)) 
            (ptd-ua lift-equiv idp) (C-dimensionS n)
C-Sphere-above .(S (S n)) (S n) ltS = 
  C-SuspS (S n) (Ptd-Sphere n) ∙ C-Sphere-above (S n) n ltS
C-Sphere-above (S n) (S m) (ltSR lt) = 
  C-SuspS n (Ptd-Sphere m) ∙ C-Sphere-above n m (<-cancel-S (ltSR lt))
