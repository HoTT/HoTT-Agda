{-# OPTIONS --without-K #-}

open import BaseOver

module Spaces.FlatteningTypes {i j k}
  (A : Set i) (B : Set j) (f g : B → A)
  (C : A → Set k) (D : (b : B) → C (f b) ≃ C (g b)) where

ijk = max i (max j k)

module BaseHIT where
  {-
    data W : Set where
      cc : A → W
      pp : (b : B) → cc (f b) ≡ cc (g b)
  -}

  private
    data #W : Set ijk where
      #cc : A → #W

  W : Set ijk
  W = #W

  cc : A → W
  cc = #cc

  postulate
    pp : (b : B) → cc (f b) ≡ cc (g b)

  W-rec : ∀ {ℓ} (P : W → Set ℓ) (cc* : (a : A) → P (cc a))
    (pp* : (b : B) → cc* (f b) ≡[ P ↓ pp b ] cc* (g b))
    → ((w : W) → P w)
  W-rec P cc* pp* (#cc a) = cc* a

  postulate
    W-rec-β : ∀ {ℓ} (P : W → Set ℓ) (cc* : (a : A) → P (cc a))
      (pp* : (b : B) → cc* (f b) ≡[ P ↓ pp b ] cc* (g b))
      → ((b : B) → apd (W-rec P cc* pp*) (pp b) ≡ pp* b)

  W-rec-nondep : ∀ {ℓ} (P : Set ℓ) (cc* : A → P)
    (pp* : (b : B) → cc* (f b) ≡ cc* (g b))
    → (W → P)
  W-rec-nondep P cc* pp* (#cc a) = cc* a

  postulate
    W-rec-nondep-β : ∀ {ℓ} (P : Set ℓ) (cc* : A → P)
      (pp* : (b : B) → cc* (f b) ≡ cc* (g b))
      → ((b : B) → ap (W-rec-nondep P cc* pp*) (pp b) ≡ pp* b)

open BaseHIT public

module FlattenedHIT where
  {-
    data Wt : Set where
      cct : (a : A) → C a → Wt
      pp : (b : B) (d : C (f b)) → cct (f b) d ≡ cct (g b) (π₁ (D b) d)
  -}

  private
    data #Wt : Set ijk where
      #cct : (a : A) (c : C a) → #Wt

  Wt : Set ijk
  Wt = #Wt

  cct : (a : A) → C a → Wt
  cct = #cct

  postulate
    ppt : (b : B) (d : C (f b)) → cct (f b) d ≡ cct (g b) (π₁ (D b) d)

  Wt-rec : ∀ {ℓ} (P : Wt → Set ℓ) (cct* : (a : A) (c : C a) → P (cct a c))
    (ppt* : (b : B) (d : C (f b)) →
           cct* (f b) d ≡[ P ↓ ppt b d ] cct* (g b) (π₁ (D b) d))
    → ((w : Wt) → P w)
  Wt-rec P cct* ppt* (#cct a c) = cct* a c

  postulate
    Wt-rec-β : ∀ {ℓ} (P : Wt → Set ℓ) (cct* : (a : A) (c : C a) → P (cct a c))
      (ppt* : (b : B) (d : C (f b)) →
             cct* (f b) d ≡[ P ↓ ppt b d ] cct* (g b) (π₁ (D b) d))
      → ((b : B) (d : C (f b)) → apd (Wt-rec P cct* ppt*) (ppt b d) ≡ ppt* b d)

  Wt-rec-nondep : ∀ {ℓ} (P : Set ℓ) (cct* : (a : A) → C a → P)
    (ppt* : (b : B) (d : C (f b)) → cct* (f b) d ≡ cct* (g b) (π₁ (D b) d))
    → (Wt → P)
  Wt-rec-nondep P cct* ppt* (#cct a c) = cct* a c

  postulate
    Wt-rec-nondep-β : ∀ {ℓ} (P : Set ℓ) (cct* : (a : A) → C a → P)
      (ppt* : (b : B) (d : C (f b)) → cct* (f b) d ≡ cct* (g b) (π₁ (D b) d))
      → ((b : B) (d : C (f b))
        → ap (Wt-rec-nondep P cct* ppt*) (ppt b d) ≡ ppt* b d)

open FlattenedHIT public

-- Here is the fibration

D-eq : (b : B) → C (f b) ≡ C (g b)
D-eq b = ua-in (D b)

P : W → Set k
P = W-rec-nondep _ C D-eq

pp-path : (b : B) (d : C (f b)) → π₁ (ua-out (ap P (pp b))) d ≡ π₁ (D b) d
pp-path b d =
  π₁ (ua-out (ap P (pp b))) d
            ≡⟨ W-rec-nondep-β _ C D-eq _ |in-ctx (λ u → π₁ (ua-out u) d) ⟩
  π₁ (ua-out (ua-in (D b))) d
            ≡⟨ ua-β (D b) |in-ctx (λ u → π₁ u d) ⟩
  π₁ (D b) d ∎

lem : ∀ {i} {A : Set i} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → ! p ∘ (p ∘' q) ≡ q
lem refl refl = refl

-- Dependent path in [P] over [pp b]
module _ {b : B} {d : C (f b)} {d' : C (g b)} where
  ↓-pp-in : (π₁ (D b) d ≡ d' → d ≡[ P ↓ pp b ] d')
  ↓-pp-in p = to-transp-in P (pp b) (pp-path b d ∘' p)

  ↓-pp-out : (d ≡[ P ↓ pp b ] d' → π₁ (D b) d ≡ d')
  ↓-pp-out p = ! (pp-path b d) ∘ to-transp-out p

  ↓-pp-β : (q : π₁ (D b) d ≡ d') → ↓-pp-out (↓-pp-in q) ≡ q
  ↓-pp-β q =
    ↓-pp-out (↓-pp-in q)
               ≡⟨ refl ⟩
    ! (pp-path b d) ∘ to-transp-out (to-transp-in P (pp b) (pp-path b d ∘' q))
               ≡⟨ to-transp-β P (pp b) (pp-path b d ∘' q) |in-ctx (λ u → ! (pp-path b d) ∘ u) ⟩
    ! (pp-path b d) ∘ (pp-path b d ∘' q)
               ≡⟨ lem (pp-path b d) q ⟩
    q ∎
