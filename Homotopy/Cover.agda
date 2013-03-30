{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

-- TODO Use pType i?
module Homotopy.Cover {i} (A : Set i) (a : A)
  (A-is-conn : is-connected ⟨0⟩ A) where

open import HLevel
open import Homotopy.Truncation
open import Homotopy.PathTruncation
open import Homotopy.Pointed
open import Integers
open import Homotopy.HomotopyGroups
open import Spaces.Pi0Paths
open import Algebra.Groups

record covering : Set (suc i) where
  constructor cov_,_
  field
    fiber : A → Set i
    fiber-is-set : ∀ a → is-set (fiber a)

is-universal : covering → Set i
is-universal (cov fiber , _) = is-connected ⟨1⟩ $ Σ A fiber

-- In terms of connectedness
universal-covering : Set (suc i)
universal-covering = Σ covering is-universal

module Reconstruct where
  module G = Pregroup (Group.g (πⁿ-group 1 (A , a)))

  -- The right group action with respect to the π¹ ( A , a )
  -- Y should be some set, but that condition is not needed
  -- in the definition.
  record action (Y : Set i) : Set (suc i) where
    constructor act_,_,_
    field
      _∙_ : Y → G.∣_∣ → Y
      right-unit : ∀ y → y ∙ G.e ≡ y
      assoc : ∀ y p₁ p₂ → (y ∙ p₁) ∙ p₂ ≡ y ∙ (p₁ G.∙ p₂)

  -- The HIT ribbon---reconstructed covering space
  module _ {Y} (act : action Y) where
    open action act
    private
      data #ribbon (a₂ : A) : Set i where
        #strip : Y →  a ≡₀ a₂ → #ribbon a₂

    ribbon : A → Set i
    ribbon = #ribbon

    strip : ∀ {a₂} → Y → a ≡₀ a₂ → ribbon a₂
    strip = #strip

    postulate
      ribbon-is-set : ∀ a₂ → is-set (ribbon a₂)
      paste : ∀ {a₂} y loop (p : a ≡₀ a₂)
        → strip (y ∙ loop) p ≡ strip y (loop ∘₀ p)

    ribbon-rec : ∀ a₂ {j} (P : ribbon a₂ → Set j)
      ⦃ P-is-set : ∀ r → is-set (P r) ⦄
      (strip* : ∀ y p → P (strip y p))
      (paste* : ∀ y loop p → transport P (paste y loop p) (strip* (y ∙ loop) p)
                           ≡ strip* y (loop ∘₀ p))
      → (∀ r → P r)
    ribbon-rec a₂ P strip* paste* (#strip y p) = strip* y p

-- The following is still a mess.  Don't read it.
module _ (uc : universal-covering) where
  open covering (π₁ uc)

  path⇒deck : ∀ {a₂} → a ≡ a₂ → fiber a → fiber a₂
  path⇒deck = transport fiber

  path₀⇒deck : ∀ {a₂} → a ≡₀ a₂ → fiber a → fiber a₂
  path₀⇒deck {a₂} = π₀-extend-nondep
    ⦃ →-is-set $ fiber-is-set a₂ ⦄ path⇒deck

  path⇒deck-is-equiv : ∀ {a₂} (path : a ≡ a₂) → is-equiv (path⇒deck path)
  path⇒deck-is-equiv path = iso-is-eq
    (transport fiber path)
    (transport fiber (! path))
    (trans-trans-opposite fiber path)
    (trans-opposite-trans fiber path)

  is-nature : (fiber a → fiber a) → Set i
  is-nature f = (p : a ≡ a)
    → ∀ x → transport fiber p (f x) ≡ f (transport fiber p x)

  auto : Set i
  auto = fiber a ≃ fiber a

  -- This Lemma can be made more general as "(m+1)-connected => has-all-paths_m"
  uc-has-all-path₀ : ∀ (p q : Σ A fiber) → p ≡₀ q
  uc-has-all-path₀ p q = inverse τ-path-equiv-path-τ-S
    $ π₂ (π₂ uc) (proj p) ∘ ! (π₂ (π₂ uc) $ proj q)

  nature-auto-eq : ∀ (f₁ f₂ : auto)
    → (f₁-is-nature : is-nature (π₁ f₁))
    → (f₂-is-nature : is-nature (π₁ f₂))
    → Σ (fiber a) (λ x → f₁ ☆ x ≡ f₂ ☆ x)
    → f₁ ≡ f₂
  nature-auto-eq f₁ f₂ f₁-nat f₂-nat (x , path) = equiv-eq $ funext λ y →
    π₀-extend
      ⦃ λ _ → ≡-is-set {x = f₁ ☆ y} {y = f₂ ☆ y} $ fiber-is-set a ⦄
      (λ uc-path →
        f₁ ☆ y
          ≡⟨ ap (π₁ f₁) $ ! $ fiber-path uc-path ⟩
        f₁ ☆ transport fiber (base-path uc-path) x
          ≡⟨ ! $ f₁-nat (base-path uc-path) x ⟩
        transport fiber (base-path uc-path) (f₁ ☆ x)
          ≡⟨ ap (transport fiber $ base-path uc-path) path ⟩
        transport fiber (base-path uc-path) (f₂ ☆ x)
          ≡⟨ f₂-nat (base-path uc-path) x ⟩
        f₂ ☆ transport fiber (base-path uc-path) x
          ≡⟨ ap (π₁ f₂) $ fiber-path uc-path ⟩∎
        f₂ ☆ y
          ∎)
      (uc-has-all-path₀ (a , x) (a , y))
