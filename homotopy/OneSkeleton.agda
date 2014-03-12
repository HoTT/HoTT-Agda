{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.OneSkeleton {i} {A : Type i} {j} {B : Type j} where

  private
    module _ (map : A → B) where
      data #OneSkeleton-aux : Type i where
        #point : A → #OneSkeleton-aux

      data #OneSkeleton : Type i where
        #one-skeleton : #OneSkeleton-aux → (Unit → Unit) → #OneSkeleton

  OneSkeleton : (A → B) → Type i
  OneSkeleton = #OneSkeleton

  module _ {map : A → B} where

    point : A → OneSkeleton map
    point a = #one-skeleton (#point a) _

    postulate  -- HIT
      link : ∀ a₁ a₂ → map a₁ == map a₂ → point a₁ == point a₂
    
    module OneSkeletonElim
      {l} {P : OneSkeleton map → Type l}
      (point* : ∀ a → P (point a))
      (link* : ∀ a₁ a₂ p → point* a₁ == point* a₂ [ P ↓ link a₁ a₂ p ]) where

      f : Π (OneSkeleton map) P
      f = f-aux phantom where

        f-aux : Phantom link* → Π (OneSkeleton map) P
        f-aux phantom (#one-skeleton (#point a) _) = point* a

      postulate
        link-β : ∀ a₁ a₂ p → apd f (link a₁ a₂ p) == link* a₁ a₂ p

    open OneSkeletonElim public using () renaming (f to OneSkeleton-elim)

    module OneSkeletonRec
      {l} {P : Type l}
      (point* : ∀ a → P)
      (link* : ∀ a₁ a₂ p → point* a₁ == point* a₂) where
      
      private
        module M = OneSkeletonElim point*
          (λ a₁ a₂ p → ↓-cst-in (link* a₁ a₂ p))

      f : OneSkeleton map → P
      f = M.f

      link-β : ∀ a₁ a₂ p → ap f (link a₁ a₂ p) == link* a₁ a₂ p
      link-β a₁ a₂ p = apd=cst-in {f = f} (M.link-β a₁ a₂ p)

    open OneSkeletonRec public using () renaming (f to OneSkeleton-rec)

    OneSkeleton-lift : OneSkeleton map → B
    OneSkeleton-lift = OneSkeleton-rec map (λ _ _ p → p)

{-
module _ {i} {A B : Set i} where
  skeleton₁ : (A → B) → Set i
  skeleton₁ f = Graveyard.skeleton₁ {i} {A} {B} {f}

-}
