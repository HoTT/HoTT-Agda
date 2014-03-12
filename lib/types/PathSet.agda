{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.TLevel
open import lib.types.Pi
open import lib.types.Truncation

-- This module is dedicated to [Trunc ⟨0⟩ (x == y)]

module lib.types.PathSet where

_=₀_ : ∀ {i} {A : Type i} → A → A → Type i
_=₀_ x y = Trunc ⟨0⟩ (x == y)

_=0_ : ∀ {i} {A : Type i} → A → A → Type i
_=0_ = _=₀_

infix 8 _∙₀_  -- \.\0
_∙₀_ : ∀ {i} {A : Type i} {x y z : A} → x =₀ y → y =₀ z → x =₀ z
_∙₀_ = Trunc-fmap2 _∙_

!₀ : ∀ {i} {A : Type i} {x y : A} → x =₀ y → y =₀ x
!₀ = Trunc-fmap !

idp₀ : ∀ {i} {A : Type i} {a : A} → a =₀ a
idp₀ = [ idp ]

ap₀ : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B)
  → x =₀ y → f x =₀ f y
ap₀ f = Trunc-rec Trunc-level ([_] ∘ ap f)

coe₀ : ∀ {i} {A B : Type i} (_ : is-set B) (p : A =₀ B) → A → B
coe₀ B-level = Trunc-rec (→-is-set B-level) coe

transport₀ : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A}
  (B-level : is-set (B y)) (p : x =₀ y) → (B x → B y)
transport₀ B B-level p = coe₀ B-level (ap₀ B p)

module _ {i} {A : Type i} where

  abstract
    ∙₀-unit-r : ∀ {x y : A} (q : x =₀ y) → (q ∙₀ idp₀) == q
    ∙₀-unit-r = Trunc-elim
      (λ _ →  =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → ap [_] $ ∙-unit-r p)

    ∙₀-unit-l : ∀ {x y : A} (q : x =₀ y) → (idp₀ ∙₀ q) == q
    ∙₀-unit-l = Trunc-elim
      (λ _ →  =-preserves-level ⟨0⟩ Trunc-level)
      (λ _ → idp)

    ∙₀-assoc : {x y z t : A} (p : x =₀ y) (q : y =₀ z) (r : z =₀ t)
      → (p ∙₀ q) ∙₀ r == p ∙₀ (q ∙₀ r)
    ∙₀-assoc = Trunc-elim
      (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → Trunc-elim
        (λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ Trunc-level)
        (λ q → Trunc-elim
          (λ _ → =-preserves-level ⟨0⟩ Trunc-level)
          (λ r → ap [_] $ ∙-assoc p q r)))
  
    !₀-inv-l : {x y : A} (p : x =₀ y) → (!₀ p) ∙₀ p == idp₀
    !₀-inv-l = Trunc-elim
      (λ _ →  =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → ap [_] $ !-inv-l p)
  
    !₀-inv-r : {x y : A} (p : x =₀ y) → p ∙₀ (!₀ p) == idp₀
    !₀-inv-r = Trunc-elim
      (λ _ →  =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → ap [_] $ !-inv-r p)
  
    ∙₀-ap₀ : ∀ {j} {B : Type j} (f : A → B) {x y z : A} (p : x =₀ y) (q : y =₀ z)
      → ap₀ f p ∙₀ ap₀ f q == ap₀ f (p ∙₀ q)
    ∙₀-ap₀ f = Trunc-elim
      (λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → Trunc-elim
        (λ _ → =-preserves-level ⟨0⟩ Trunc-level)
        (λ q → ap [_] $ ∙-ap f p q))
  
    ap₀-∘ : ∀ {j k} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
      {x y : A} (p : x =₀ y) → ap₀ (g ∘ f) p == ap₀ g (ap₀ f p)
    ap₀-∘ f g = Trunc-elim
      (λ _ → =-preserves-level ⟨0⟩ Trunc-level)
      (λ p → ap [_] $ ap-∘ f g p)

    coe₀-∙₀ : {B C : Type i} (B-level : is-set B) (C-level : is-set C)
      → (p : A =₀ B) (q : B =₀ C) (a : A)
      → coe₀ C-level (p ∙₀ q) a == coe₀ C-level q (coe₀ B-level p a)
    coe₀-∙₀ B-level C-level = Trunc-elim
      (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ C-level)
      (λ p → Trunc-elim
        (λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ C-level)
        (λ q a → coe-∙ p q a))

    trans₀-∙₀ : ∀ {j} {B : A → Type j}
      → (B-level : ∀ {a} → is-set (B a))
      → {x y z : A} (p : x =₀ y) (q : y =₀ z) (b : B x)
      → transport₀ B B-level (p ∙₀ q) b
      == transport₀ B B-level q (transport₀ B B-level p b)
    trans₀-∙₀ B-level = Trunc-elim
      (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ B-level)
      (λ p → Trunc-elim
        (λ _ → Π-is-set λ _ → =-preserves-level ⟨0⟩ B-level)
        (λ q b → trans-∙ p q b))

{-
module _ {i} {A : Type i} where
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
-}
