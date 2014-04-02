{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Lift

module lib.groups.Lift where

Lift-group-structure : ∀ {i j} {A : Type i} 
  → GroupStructure A → GroupStructure (Lift {j = j} A)
Lift-group-structure GS = record 
  { ident = lift ident
  ; inv = λ {(lift x) → lift (inv x)}
  ; comp = λ {(lift x) (lift y) → lift (comp x y)}
  ; unitl = λ {(lift y) → ap lift (unitl y)}
  ; unitr = λ {(lift x) → ap lift (unitr x)}
  ; assoc = λ {(lift x) (lift y) (lift z) → ap lift (assoc x y z)}
  ; invr = λ {(lift x) → ap lift (invr x)}
  ; invl = λ {(lift x) → ap lift (invl x)}
  }
  where open GroupStructure GS

Lift-Group : ∀ {i j} → Group i → Group (lmax i j)
Lift-Group {j = j} G = group (Lift {j = j} El) (Lift-level El-level) 
                             (Lift-group-structure group-struct)
  where open Group G
