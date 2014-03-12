{-# OPTIONS --without-K --copatterns #-}

open import HoTT

module experimental.TwoSkeleton {i} {A : Type i} {j} {B : Type j} where

module _ where
  private
    module _ (map : A → B) where
      data #TwoSkeleton-aux : Type i where
        #point : A → #TwoSkeleton-aux

      data #TwoSkeleton : Type i where
        #two-skeleton : #TwoSkeleton-aux → (Unit → Unit) → #TwoSkeleton

  TwoSkeleton : (A → B) → Type i
  TwoSkeleton = #TwoSkeleton

  module _ {map : A → B} where

    point : A → TwoSkeleton map
    point a = #two-skeleton (#point a) _

    postulate  -- HIT
      link₀ : ∀ a₁ a₂ → map a₁ == map a₂ → point a₁ == point a₂

      link₁ : ∀ a₁ a₂ a₃ (p₁ : map a₁ == map a₂) (p₂ : map a₂ == map a₃)
            → link₀ a₁ a₂ p₁ ∙' link₀ a₂ a₃ p₂ == link₀ a₁ a₃ (p₁ ∙' p₂)

    module TwoSkeletonElim
      {l} {P : TwoSkeleton map → Type l}
      (point* : ∀ a → P (point a))
      (link₀* : ∀ a₁ a₂ p → point* a₁ == point* a₂ [ P ↓ link₀ a₁ a₂ p ])
      (link₁* : ∀ a₁ a₂ a₃ p₁ p₂
        →  link₀* a₁ a₂ p₁ ∙'ᵈ link₀* a₂ a₃ p₂
        == link₀* a₁ a₃ (p₁ ∙' p₂)
        [ (λ p → PathOver P p (point* a₁) (point* a₃)) ↓ link₁ a₁ a₂ a₃ p₁ p₂ ]) where

      f : Π (TwoSkeleton map) P
      f = f-aux phantom phantom where

        f-aux : Phantom link₀* → Phantom link₁* → Π (TwoSkeleton map) P
        f-aux phantom phantom (#two-skeleton (#point a) _) = point* a

      postulate  -- HIT
        link₀-β : ∀ a₁ a₂ p → apd f (link₀ a₁ a₂ p) == link₀* a₁ a₂ p

      private
        lemma : ∀ a₁ a₂ a₃ p₁ p₂
              → apd f (link₀ a₁ a₂ p₁ ∙' link₀ a₂ a₃ p₂)
             == link₀* a₁ a₂ p₁ ∙'ᵈ link₀* a₂ a₃ p₂
        lemma a₁ a₂ a₃ p₁ p₂ =
          apd f (link₀ a₁ a₂ p₁ ∙' link₀ a₂ a₃ p₂)
            =⟨ apd-∙' f (link₀ a₁ a₂ p₁) (link₀ a₂ a₃ p₂) ⟩
          apd f (link₀ a₁ a₂ p₁) ∙'ᵈ apd f (link₀ a₂ a₃ p₂)
            =⟨ link₀-β a₁ a₂ p₁ |in-ctx (λ u → u ∙'ᵈ apd f (link₀ a₂ a₃ p₂)) ⟩
          link₀* a₁ a₂ p₁ ∙'ᵈ apd f (link₀ a₂ a₃ p₂)
            =⟨ link₀-β a₂ a₃ p₂ |in-ctx (λ u → link₀* a₁ a₂ p₁ ∙'ᵈ u) ⟩
          link₀* a₁ a₂ p₁ ∙'ᵈ link₀* a₂ a₃ p₂
            ∎

      postulate  -- HIT
        link₁-β : ∀ a₁ a₂ a₃ p₁ p₂
                → apd (apd f) (link₁ a₁ a₂ a₃ p₁ p₂)
               == lemma a₁ a₂ a₃ p₁ p₂ ◃ (link₁* a₁ a₂ a₃ p₁ p₂ ▹! link₀-β a₁ a₃ (p₁ ∙' p₂))

open TwoSkeletonElim public using () renaming (f to TwoSkeleton-elim)

module TwoSkeletonRec {map : A → B} {l} {P : Type l}
  (point* : ∀ a → P)
  (link₀* : ∀ a₁ a₂ p → point* a₁ == point* a₂)
  (link₁* : ∀ a₁ a₂ a₃ (p₁ : map a₁ == map a₂) (p₂ : map a₂ == map a₃)
            → link₀* a₁ a₂ p₁ ∙' link₀* a₂ a₃ p₂
           == link₀* a₁ a₃ (p₁ ∙' p₂)) where

  private
    module M = TwoSkeletonElim {l = l} {P = λ _ → P}
      point*
      (λ a₁ a₂ p → ↓-cst-in (link₀* a₁ a₂ p))
      (λ a₁ a₂ a₃ p₁ p₂
        → ↓-cst-in-∙' (link₀ a₁ a₂ p₁) (link₀ a₂ a₃ p₂) (link₀* a₁ a₂ p₁) (link₀* a₂ a₃ p₂)
       !◃ ↓-cst-in2 (link₁* a₁ a₂ a₃ p₁ p₂))

  f : TwoSkeleton map → P
  f = M.f

  link₀-β : ∀ a₁ a₂ p → ap f (link₀ a₁ a₂ p) == link₀* a₁ a₂ p
  link₀-β a₁ a₂ p = apd=cst-in {f = f} $ M.link₀-β a₁ a₂ p

  private
    lemma : ∀ a₁ a₂ a₃ p₁ p₂
          → ap f (link₀ a₁ a₂ p₁ ∙' link₀ a₂ a₃ p₂)
         == link₀* a₁ a₂ p₁ ∙' link₀* a₂ a₃ p₂
    lemma a₁ a₂ a₃ p₁ p₂ =
      ap f (link₀ a₁ a₂ p₁ ∙' link₀ a₂ a₃ p₂)
        =⟨ ap-∙' f (link₀ a₁ a₂ p₁) (link₀ a₂ a₃ p₂) ⟩
      ap f (link₀ a₁ a₂ p₁) ∙' ap f (link₀ a₂ a₃ p₂)
        =⟨ link₀-β a₁ a₂ p₁ |in-ctx (λ u → u ∙' ap f (link₀ a₂ a₃ p₂)) ⟩
      link₀* a₁ a₂ p₁ ∙' ap f (link₀ a₂ a₃ p₂)
        =⟨ link₀-β a₂ a₃ p₂ |in-ctx (λ u → link₀* a₁ a₂ p₁ ∙' u) ⟩
      link₀* a₁ a₂ p₁ ∙' link₀* a₂ a₃ p₂
        ∎

  -- I am a lazy person.
  postulate  -- HIT
    link₁-β : ∀ a₁ a₂ a₃ p₁ p₂
            → ap (ap f) (link₁ a₁ a₂ a₃ p₁ p₂)
           == (lemma a₁ a₂ a₃ p₁ p₂ ∙ link₁* a₁ a₂ a₃ p₁ p₂) ∙ (! $ link₀-β a₁ a₃ (p₁ ∙' p₂))
