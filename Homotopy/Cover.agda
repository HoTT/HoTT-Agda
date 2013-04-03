{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pointed
open import Homotopy.Connected

-- TODO Use pType i?
module Homotopy.Cover {i} (A⋆ : pType i)
  (A-is-conn : is-connected ⟨0⟩ ∣ A⋆ ∣) where
open pType A⋆ renaming (∣_∣ to A ; ⋆ to a)

open import Homotopy.Cover.Def A

module Reconstruct where
  open import Homotopy.Cover.HomotopyGroupSetIsomorphism A⋆ A-is-conn public

{-
-- The following is still a mess.  Don't read it.
module _ (uc : universal-covering) where
  open covering (π₁ uc)

{-
  path⇒deck-is-equiv : ∀ {a₂} (path : a ≡ a₂) → is-equiv (path⇒deck path)
  path⇒deck-is-equiv path = iso-is-eq
    (transport fiber path)
    (transport fiber (! path))
    (trans-trans-opposite fiber path)
    (trans-opposite-trans fiber path)
-}

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
-}
