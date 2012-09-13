{-# OPTIONS --without-K #-}
{-# OPTIONS --termination-depth=2 #-}

open import Base
open import Topology.Spheres
open import Topology.Suspension
open import Integers.Integers

module Truncation.SphereFillings where

-- Warning: Here "n-sphere" means sphere of dimension (n - 1)
-- Filling n-spheres gives something of h-level n

-- Definition of fillings of a sphere
filling : ∀ {i} (n : ℕ) {A : Set i} (f : Sⁿ n → A) → Set i
filling {i} n {A} f = Σ A (λ t → ((x : Sⁿ n) → t ≡ f x))

-- Definition of dependent fillings of a sphere above a ball
filling-dep : ∀ {i j} (n : ℕ) {A : Set i} (P : A → Set j) (f : Sⁿ n → A)
  (fill : filling n f) (p : (x : Sⁿ n) → P (f x)) → Set j
filling-dep {i} {j} n {A} P f fill p =
  Σ (P (π₁ fill)) (λ t → ((x : Sⁿ n) → transport P (π₂ fill x) t ≡ p x))

-- [has-n-spheres-filled n A] is inhabited iff every n-sphere in [A] can be
-- filled with an (n+1)-ball.
-- We will show that this is equivalent to being of h-level n, *for n > 0*
-- (for n = 0, having 0-spheres filled only means that A is inhabited)
has-n-spheres-filled : ∀ {i} (n : ℕ) (A : Set i) → Set i
has-n-spheres-filled n A = (f : Sⁿ n → A) → filling n f

-- [has-n-spheres-filled] satisfy the same inductive property than [is-hlevel]
fill-paths : ∀ {i} (n : ℕ) (A : Set i) (t : has-n-spheres-filled (S n) A)
  → ((x y : A) → has-n-spheres-filled n (x ≡ y))
fill-paths n A t x y f =
  ((! (π₂ u (north _)) ∘ π₂ u (south _))
  , (λ z → ! (lemma (paths _ z)) ∘ suspension-β-paths-nondep _ _ _ _ _ _)) where

  -- [f] is a map from [Sⁿ n] to [x ≡ y], we can build from it a map
  -- from [Sⁿ (S n)] to [A]
  newf : Sⁿ (S n) → A
  newf = suspension-rec-nondep _ _ x y f

  u : filling (S n) newf
  u = t newf
  -- I’ve got a filling
  
  -- Every path in the sphere is equal (in A) to the canonical path going
  -- through the center of the filled sphere
  lemma : {p q : Sⁿ (S n)} (l : p ≡ q) → map newf l ≡ ! (π₂ u p) ∘ π₂ u q
  lemma (refl a) = ! (opposite-left-inverse (π₂ u a))

-- We first prove that if n-spheres are filled, then the type is of
-- h-level (S n), we have to prove it for n = 1, and then use the previous lemma
abstract
  n-spheres-filled-hlevel : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i)
    (t : has-n-spheres-filled n A) → is-hlevel n A
  n-spheres-filled-hlevel 0 ⦃ >0 ⦄ A t = abort (>0 (refl 0))
  n-spheres-filled-hlevel 1 A t =
    all-paths-is-prop (λ x y → ! (π₂ (u x y) (north _)) ∘ π₂ (u x y) (south _))
    where
    u : (x y : A)
        → Σ A (λ t' → (u : Sⁿ 1) → t' ≡ suspension-rec-nondep ⊥ A x y abort u)
    u = λ x y → t (suspension-rec-nondep ⊥ A x y abort)
  n-spheres-filled-hlevel (S (S n)) A t =
    λ x y → n-spheres-filled-hlevel (S n) (x ≡ y) (fill-paths (S n) A t x y)
    where
    -- I don’t know how to make Agda guess this automatically
    >0 : S n ≢ 0
    >0 = ℕ-Sn≢O n

-- We now prove the converse
abstract
  hlevel-n-has-n-spheres-filled : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i)
    (t : is-hlevel n A) → has-n-spheres-filled n A
  hlevel-n-has-n-spheres-filled 0 ⦃ >0 ⦄ A t f = abort (>0 (refl 0))
  hlevel-n-has-n-spheres-filled 1 A t f = (f (north _) , (λ x → π₁ (t _ _)))
  hlevel-n-has-n-spheres-filled (S (S n)) A t f =
    (f (north _)
    , (suspension-rec _ _ (refl _) (map f (paths _ (north _)))
        (λ x → trans-a≡fx (f (north _)) f (paths _ _) _
               ∘ (! (π₂ filled-newf x) ∘ π₂ filled-newf (north _))))) where
  
    newf : Sⁿ (S n) → (f (north (Sⁿ (S n))) ≡ f (south (Sⁿ (S n))))
    newf x = map f (paths _ x)
  
    >0 : S n ≢ 0
    >0 = ℕ-Sn≢O n
  
    filled-newf : filling (S n) newf
    filled-newf = hlevel-n-has-n-spheres-filled (S n) _ (t _ _) newf

-- Should be moved somewhere else
-- trans-pi : ∀ {i j k} {A : Set i} {B : Set j} (Q : A → B → Set k) {u v : A}
--   (p : u ≡ v) (f : (y : B) → Q u y) (q : B) →
--   transport (λ x → (y : B) → Q x y) p f q ≡ transport (λ t → Q t q) p (f q)
-- trans-pi Q (refl _) f q = refl _

filling-has-all-paths : ∀ {i} (n : ℕ) ⦃ >0 : n ≢ 0 ⦄ (A : Set i)
  ⦃ fill : has-n-spheres-filled (S n) A ⦄ (f : Sⁿ n → A)
  → has-all-paths (filling n f)
filling-has-all-paths n A ⦃ fill ⦄ f fill₁ fill₂ =
  total-path (! (π₂ big-map-filled (north _)) ∘ π₂ big-map-filled (south _))
  (funext-dep (λ x →
                   trans-A→Pxy _ (λ t x₁ → t ≡ f x₁)
                   (! (π₂ big-map-filled (north (Sⁿ n))) ∘
                    π₂ big-map-filled (south (Sⁿ n)))
                   (π₂ fill₁) x
                   ∘ (trans-x≡a
                        (! (π₂ big-map-filled (north (Sⁿ n))) ∘
                         π₂ big-map-filled (south (Sⁿ n)))
                        (π₂ fill₁ x)
                   ∘ move!-right-on-left
                       (! (π₂ big-map-filled (north (Sⁿ n))) ∘
                        π₂ big-map-filled (south (Sⁿ n)))
                       _ _
                    (move-left-on-right _
                       (! (π₂ big-map-filled (north (Sⁿ n))) ∘
                        π₂ big-map-filled (south (Sⁿ n)))
                       _
                    (! (suspension-β-paths-nondep _ _ _ _ _ x)
                     ∘ lemma (paths _ x)))))) where

  big-map : Sⁿ (S n) → A
  big-map = suspension-rec-nondep _ _ (π₁ fill₁) (π₁ fill₂)
                                  (λ x → π₂ fill₁ x ∘ ! (π₂ fill₂ x))

  big-map-filled : filling (S n) big-map
  big-map-filled = fill big-map

  lemma : {u v : Sⁿ (S n)} (p : u ≡ v)
    → map big-map p ≡ (! (π₂ big-map-filled u) ∘  π₂ big-map-filled v)
  lemma (refl a) = ! (opposite-left-inverse (π₂ big-map-filled a))

abstract
  hlevel-n-has-filling-dep : ∀ {i j} (A : Set i) (P : A → Set j) (n : ℕ)
    ⦃ >0 : n ≢ 0 ⦄ ⦃ trunc : (x : A) → is-hlevel n (P x) ⦄
    (fill : has-n-spheres-filled n A) (f : Sⁿ n → A) (p : (x : Sⁿ n) → P (f x))
    → filling-dep n P f (fill f) p
  hlevel-n-has-filling-dep A P n ⦃ >0 ⦄ ⦃ trunc ⦄ fill f p =
    transport (λ t → filling-dep n P f t p) eq fill-dep  where
    
    -- Combining [f] and [p] we have a sphere in the total space of [P]
    newf : Sⁿ n → Σ A P
    newf x = (f x , p x)
    
    -- But this total space is of h-level [n]
    ΣAP-hlevel : is-hlevel n (Σ A P)
    ΣAP-hlevel = sigma-hlevel n (n-spheres-filled-hlevel n A fill) trunc
    
    -- Hence the sphere is filled
    tot-fill : filling n newf
    tot-fill = hlevel-n-has-n-spheres-filled n (Σ A P) ΣAP-hlevel newf
  
    -- We can split this filling as a filling of [f] in [A] …
    new-fill : filling n f
    new-fill = (π₁ (π₁ tot-fill) , (λ x → base-path (π₂ tot-fill x)))
  
    -- and a dependent filling above the previous filling of [f], along [p]
    fill-dep : filling-dep n P f new-fill p
    fill-dep = (π₂ (π₁ tot-fill) , (λ x → fiber-path (π₂ tot-fill x)))
  
    S>0 : S n ≢ 0
    S>0 = ℕ-Sn≢O n
  
    A-has-Sn-spheres-filled : has-n-spheres-filled (S n) A
    A-has-Sn-spheres-filled =
      hlevel-n-has-n-spheres-filled (S n) A
        (is-increasing-hlevel n A (n-spheres-filled-hlevel n A fill))
  
    -- But both the new and the old fillings of [f] are equal, hence we will
    -- have a dependent filling above the old one
    eq : new-fill ≡ fill f
    eq = filling-has-all-paths n A f new-fill (fill f)
