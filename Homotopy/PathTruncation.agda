{-# OPTIONS --without-K #-}

{-
  Now it only has specialized constructs and lemmas for π₀ (x ≡ y)

  Should be rewritten with something like Algebra.Groupoids
-}

open import Base

module Homotopy.PathTruncation where

open import HLevel
open import HLevelBis
open import Homotopy.Truncation

_≡₀_ : ∀ {i} {A : Set i} → A → A → Set i
_≡₀_ x y = π₀ (x ≡ y)

infix 8 _∘₀_  -- \o\0
_∘₀_ : ∀ {i} {A : Set i} {x y z : A} → x ≡₀ y → y ≡₀ z → x ≡₀ z
_∘₀_ =
  π₀-extend-nondep ⦃ →-is-set $ π₀-is-set _ ⦄ (λ p →
    π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (λ q →
      proj $ p ∘ q))

!₀ : ∀ {i} {A : Set i} {x y : A} → x ≡₀ y → y ≡₀ x
!₀ = π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (proj ◯ !)

refl₀ : ∀ {i} {A : Set i} {a : A} → a ≡₀ a
refl₀ = proj refl

ap₀ : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (f : A → B)
  → x ≡₀ y → f x ≡₀ f y
ap₀ f = π₀-extend-nondep ⦃ π₀-is-set _ ⦄ (proj ◯ ap f)

module _ {i} {A : Set i} where

  refl₀-right-unit : ∀ {x y : A} (q : x ≡₀ y) → (q ∘₀ refl₀) ≡ q
  refl₀-right-unit {x = x} {y} = π₀-extend
    ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
    (λ x → ap proj $ refl-right-unit x)

  refl₀-left-unit : ∀ {x y : A} (q : x ≡₀ y) → (refl₀ ∘₀ q) ≡ q
  refl₀-left-unit {x = x} {y} = π₀-extend
    ⦃ λ _ →  ≡-is-set $ π₀-is-set (x ≡ y) ⦄
    (λ _ → refl)

  concat₀-assoc : {x y z t : A} (p : x ≡₀ y) (q : y ≡₀ z) (r : z ≡₀ t)
    → (p ∘₀ q) ∘₀ r ≡ p ∘₀ (q ∘₀ r)
  concat₀-assoc =
    π₀-extend ⦃ λ _ → Π-is-set λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ q →
        π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ r →
          ap proj $ concat-assoc p q r)))

  concat₀-ap₀ : ∀ {j} {B : Set j} (f : A → B) {x y z : A} (p : x ≡₀ y) (q : y ≡₀ z)
    → ap₀ f p ∘₀ ap₀ f q ≡ ap₀ f (p ∘₀ q)
  concat₀-ap₀ f =
    π₀-extend ⦃ λ _ → Π-is-set λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ q →
        ap proj $ concat-ap f p q))

  ap₀-compose : ∀ {j k} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x ≡₀ y) → ap₀ (g ◯ f) p ≡ ap₀ g (ap₀ f p)
  ap₀-compose f g =
    π₀-extend ⦃ λ _ → ≡-is-set $ π₀-is-set _ ⦄ (λ p →
      ap proj $ ap-compose f g p)

module _ {i} {A : Set i} where
  trans-id≡₀cst : {a b c : A} (p : b ≡ c) (q : b ≡₀ a)
    → transport (λ x → x ≡₀ a) p q ≡ proj (! p) ∘₀ q
  trans-id≡₀cst refl q = ! $ refl₀-left-unit q

  trans-cst≡₀id : {a b c : A} (p : b ≡ c) (q : a ≡₀ b)
    → transport (λ x → a ≡₀ x) p q ≡ q ∘₀ proj p
  trans-cst≡₀id refl q = ! $ refl₀-right-unit q

module _ {i} {A : Set i} where
  homotopy₀-naturality : ∀ {j} {B : Set j} (f g : A → B)
    (p : (x : A) → f x ≡₀ g x) {x y : A} (q : x ≡₀ y)
    → ap₀ f q ∘₀ p y ≡ p x ∘₀ ap₀ g q
  homotopy₀-naturality f g p {x} {y} q = π₀-extend
    ⦃ λ q → ≡-is-set {x = ap₀ f q ∘₀ p y} {y = p x ∘₀ ap₀ g q}
            $ π₀-is-set (f x ≡ g y) ⦄
    (lemma {x} {y}) q
    where
      lemma : ∀ {x y : A} (q : x ≡ y) → ap₀ f (proj q) ∘₀ p y ≡ p x ∘₀ ap₀ g (proj q)
      lemma refl =
        refl₀ ∘₀ p _
          ≡⟨ refl₀-left-unit (p _) ⟩
        p _
          ≡⟨ ! $ refl₀-right-unit _ ⟩∎
        p _ ∘₀ refl₀
          ∎

-- Loop space commutes with truncation in the sense that
-- τ n (Ω X) = Ω (τ (S n) X)
-- (actually, this is true more generally for paths spaces and we need this
-- level of generality to prove it)

module _ {i} {n : ℕ₋₂} {A : Set i} where

  private
    to : (x y : A) → (τ n (x ≡ y)) → ((proj {n = S n} x) ≡ (proj y))
    to x y = τ-extend-nondep ⦃ τ-is-truncated (S n) A _ _ ⦄ (ap proj)

    -- [truncated-path-space (proj x) (proj y)] is [τ n (x ≡ y)]
    truncated-path-space : (u v : τ (S n) A) → Type≤ n i
    truncated-path-space = τ-extend-nondep
                             ⦃ →-is-truncated (S n) (Type≤-is-truncated n _) ⦄
                             (λ x → τ-extend-nondep ⦃ Type≤-is-truncated n _ ⦄
                               (λ y → τ n (x ≡ y) , τ-is-truncated n _))

    -- We now extend [to] to the truncation of [A], and this is why we needed to
    -- first extend the return type of [to]
    to' : (u v : τ (S n) A) → (π₁ (truncated-path-space u v) → u ≡ v)
    to' = τ-extend ⦃ λ x → Π-is-truncated (S n) (λ a →
                             Π-is-truncated (S n) (λ b →
                               ≡-is-truncated (S n)
                                 (τ-is-truncated (S n) A)))⦄
            (λ x → τ-extend ⦃ λ t → Π-is-truncated (S n) (λ a →
                                      ≡-is-truncated (S n)
                                        (τ-is-truncated (S n) A))⦄
              (λ y → to x y))

    from'-refl : (u : τ (S n) A) → (π₁ (truncated-path-space u u))
    from'-refl = τ-extend ⦃ λ x → truncated-is-truncated-S n
                                    (π₂ (truncated-path-space x x))⦄
                   (λ x → proj refl)

    from' : (u v : τ (S n) A) → (u ≡ v → π₁ (truncated-path-space u v))
    from' u .u refl = from'-refl u

    from : (x y : A) → (proj {n = S n} x ≡ proj y → τ n (x ≡ y))
    from x y p = from' (proj x) (proj y) p

    from-to : (x y : A) (p : τ n (x ≡ y)) → from x y (to x y p) ≡ p
    from-to x y = τ-extend ⦃ λ _ → ≡-is-truncated n (τ-is-truncated n _)⦄
                    (from-to' x y) where

      from-to' : (x y : A) (p : x ≡ y) → from x y (to x y (proj p)) ≡ proj p
      from-to' x .x refl = refl

    to'-from' : (u v : τ (S n) A) (p : u ≡ v) → to' u v (from' u v p) ≡ p
    to'-from' x .x refl = to'-from'-refl x where
      to'-from'-refl : (u : τ (S n) A) → to' u u (from' u u refl) ≡ refl
      to'-from'-refl = τ-extend ⦃ λ _ → ≡-is-truncated (S n)
                                          (≡-is-truncated (S n)
                                            (τ-is-truncated (S n) A))⦄
                         (λ _ → refl)

    to-from : (x y : A) (p : proj {n = S n} x ≡ proj y) → to x y (from x y p) ≡ p
    to-from x y p = to'-from' (proj x) (proj y) p

  τ-path-equiv-path-τ-S : {x y : A} → τ n (x ≡ y) ≃ (proj {n = S n} x ≡ proj y)
  τ-path-equiv-path-τ-S {x} {y} =
    (to x y , iso-is-eq _ (from x y) (to-from x y) (from-to x y))

  module _ where
    open import Homotopy.Connected

    abstract
      connected-has-connected-paths : is-connected (S n) A → (p q : A) → is-connected n (p ≡ q)
      connected-has-connected-paths conn p q =
        equiv-types-truncated ⟨-2⟩ (τ-path-equiv-path-τ-S ⁻¹) (contr-is-prop conn (proj p) (proj q))

    connected-has-all-τ-paths : is-connected (S n) A → (p q : A) → τ n (p ≡ q)
    connected-has-all-τ-paths conn p q = π₁ $ connected-has-connected-paths conn p q
