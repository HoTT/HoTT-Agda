{-# OPTIONS --without-K #-}

open import Base
open import Coinduction

module CoindEquiv where

-- Coinductive equivalences
record _∼_ {i j} (A : Set i) (B : Set j) : Set (max i j) where
  constructor _,_,_
  field
    to : A → B
    from : B → A
    eq : (a : A) (b : B) → ∞ ((to a ≡ b) ∼ (a ≡ from b))

-- Identity
id-∼ : ∀ {i} (A : Set i) → A ∼ A
id-∼ A = (id A) , (id A) , (λ a b → ♯ id-∼ (a ≡ b))

-- Transitivity
trans-∼ : ∀ {i} {A B C : Set i} → A ∼ B → B ∼ C → A ∼ C
trans-∼ (to , from , eq) (to' , from' , eq') =
  ((to' ◯ to) , (from ◯ from') ,
    (λ a c → ♯ trans-∼ (♭ (eq' (to a) c)) (♭ (eq a (from' c)))))

-- -- Symmetry is harder
-- sym-∼ : ∀ {i} {A B : Set i} → A ∼ B → B ∼ A
-- sym-∼ (to , from , eq) = (from , to , (λ a b → ♯ {!sym-∼ (♭ (eq b a))!}))


-- Logical equivalence with the usual notion of equivalences

∼-to-≃ : ∀ {i j} {A : Set i} {B : Set j} → (A ∼ B → A ≃ B)
∼-to-≃ (to , from , eq) =
  (to , iso-is-eq to from (λ b → _∼_.from (♭ (eq (from b) b)) (refl _))
                          (λ a → ! (_∼_.to (♭ (eq a (to a))) (refl _))))

≃-to-∼ : ∀ {i j} {A : Set i} {B : Set j} → (A ≃ B → A ∼ B)
≃-to-∼ e = (π₁ e) , (inverse e) ,
  (λ a b → ♯ ≃-to-∼ (equiv-compose
    (path-to-eq (map (λ b → e ☆ a ≡ b) (! (inverse-right-inverse e b))))
    ((equiv-map e a (inverse e b))⁻¹)))


-- Unfinished attempt to prove that this notion is coherent

∼-eq-raw : ∀ {i j} {A : Set i} {B : Set j}
  {f f' : A → B} (p : f ≡ f') {g g' : B → A} (q : g ≡ g')
  {eq : (a : A) (b : B) → ∞ ((f a ≡ b) ∼ (a ≡ g b))}
  {eq' : (a : A) (b : B) → ∞ ((f' a ≡ b) ∼ (a ≡ g' b))}
  (r : transport _ p (transport _ q eq) ≡ eq')
  → (f , g , eq) ≡ (f' , g' , eq')
∼-eq-raw (refl f) (refl g) (refl eq) = refl (f , g , eq)

-- ∼-eq : ∀ {i j} {A : Set i} {B : Set j}
--   {f f' : A → B} (p : (a : A) → f a ≡ f' a)
--   {g g' : B → A} (q : (b : B) → g b ≡ g' b)
--   {eq : (a : A) (b : B) → ∞ ((f a ≡ b) ∼ (a ≡ g b))}
--   {eq' : (a : A) (b : B) → ∞ ((f' a ≡ b) ∼ (a ≡ g' b))}
--   (r : (a : A) (b : B) →
--      transport (λ u → (u ≡ b) ∼ (a ≡ g' b)) (p a) (
--      transport (λ u → (f a ≡ b) ∼ (a ≡ u)) (q b) (♭ (eq a b)))
--      ≡ ♭ (eq' a b))
--   → (f , g , eq) ≡ (f' , g' , eq')
-- ∼-eq p q r = ∼-eq-raw (funext p) (funext q)
--   (funext (λ a → (funext (λ b → {!r a b!}))))

-- coherent : ∀ {i j} (A : Set i) (B : Set j) → ((A ≃ B) ≃ (A ∼ B))
-- coherent A B = (≃-to-∼ A B , iso-is-eq _ (∼-to-≃ A B)
--   (λ y → ∼-eq (λ a → refl _)
--               (λ b → happly (inverse-iso-is-eq (_∼_.to y) (_∼_.from y) _ _) b)
--               (λ a b → {!!}))
--   (λ e → Σ-eq (refl _) (π₁ (is-equiv-is-prop _ _ _))))
