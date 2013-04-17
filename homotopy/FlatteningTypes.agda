{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.FlatteningTypes {i j k}
  (A : Type i) (B : Type j) (f g : B → A)
  (C : A → Type k) (D : (b : B) → C (f b) ≃ C (g b)) where

ijk = max i (max j k)

module BaseHIT where
  {-
    data W : Type where
      cc : A → W
      pp : (b : B) → cc (f b) ≡ cc (g b)
  -}

  private
    data #W : Type ijk where
      #cc : A → #W

  W : Type ijk
  W = #W

  cc : A → W
  cc = #cc

  postulate
    pp : (b : B) → cc (f b) == cc (g b)

  W-elim : ∀ {ℓ} {P : W → Type ℓ} (cc* : (a : A) → P (cc a))
    (pp* : (b : B) → cc* (f b) == cc* (g b) [ P ↓ pp b ])
    → ((w : W) → P w)
  W-elim cc* pp* (#cc a) = cc* a

  postulate
    pp-β : ∀ {ℓ} {P : W → Type ℓ} (cc* : (a : A) → P (cc a))
      (pp* : (b : B) → cc* (f b) == cc* (g b) [ P ↓ pp b ])
      → ((b : B) → apd (W-elim cc* pp*) (pp b) == pp* b)

  W-rec : ∀ {ℓ} {P : Type ℓ} (cc* : A → P)
    (pp* : (b : B) → cc* (f b) == cc* (g b))
    → (W → P)
  W-rec cc* pp* (#cc a) = cc* a

  postulate
    pp-β' : ∀ {ℓ} {P : Type ℓ} (cc* : A → P)
      (pp* : (b : B) → cc* (f b) == cc* (g b))
      → ((b : B) → ap (W-rec cc* pp*) (pp b) == pp* b)

open BaseHIT public

module FlattenedHIT where
  {-
    data Wt : Type where
      cct : (a : A) → C a → Wt
      pp : (b : B) (d : C (f b)) → cct (f b) d == cct (g b) (fst (D b) d)
  -}

  private
    data #Wt : Type ijk where
      #cct : (a : A) (c : C a) → #Wt

  Wt : Type ijk
  Wt = #Wt

  cct : (a : A) → C a → Wt
  cct = #cct

  postulate
    ppt : (b : B) (d : C (f b)) → cct (f b) d == cct (g b) (fst (D b) d)

  Wt-elim : ∀ {ℓ} {P : Wt → Type ℓ} (cct* : (a : A) (c : C a) → P (cct a c))
    (ppt* : (b : B) (d : C (f b)) →
           cct* (f b) d == cct* (g b) (fst (D b) d) [ P ↓ ppt b d ])
    → ((w : Wt) → P w)
  Wt-elim cct* ppt* (#cct a c) = cct* a c

  postulate
    ppt-β : ∀ {ℓ} {P : Wt → Type ℓ} (cct* : (a : A) (c : C a) → P (cct a c))
      (ppt* : (b : B) (d : C (f b)) →
             cct* (f b) d == cct* (g b) (fst (D b) d) [ P ↓ ppt b d ])
      → ((b : B) (d : C (f b)) → apd (Wt-elim cct* ppt*) (ppt b d) == ppt* b d)

  Wt-rec : ∀ {ℓ} {P : Type ℓ} (cct* : (a : A) → C a → P)
    (ppt* : (b : B) (d : C (f b)) → cct* (f b) d == cct* (g b) (fst (D b) d))
    → (Wt → P)
  Wt-rec cct* ppt* (#cct a c) = cct* a c

  postulate
    ppt-β' : ∀ {ℓ} {P : Type ℓ} (cct* : (a : A) → C a → P)
      (ppt* : (b : B) (d : C (f b)) → cct* (f b) d == cct* (g b) (fst (D b) d))
      → ((b : B) (d : C (f b))
        → ap (Wt-rec cct* ppt*) (ppt b d) == ppt* b d)

open FlattenedHIT public

-- Here is the fibration

D-path : (b : B) → C (f b) == C (g b)
D-path b = ua (D b)

P : W → Type k
P = W-rec C D-path

pp-path : (b : B) (d : C (f b)) → coe (ap P (pp b)) d == fst (D b) d
pp-path b d =
  coe (ap P (pp b)) d
            =⟨ pp-β' C D-path _ |in-ctx (λ u → coe u d) ⟩
  coe (ua (D b)) d
            =⟨ coe-β (D b) d ⟩
  fst (D b) d ∎

lem : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
  → ! p ∙ (p ∙' q) == q
lem idp idp = idp

-- Dependent path in [P] over [pp b]
module _ {b : B} {d : C (f b)} {d' : C (g b)} where
  ↓-pp-in : (fst (D b) d == d' → d == d' [ P ↓ pp b ])
  ↓-pp-in p = to-transp-in P (pp b) (pp-path b d ∙' p)

  ↓-pp-out : (d == d' [ P ↓ pp b ] → fst (D b) d == d')
  ↓-pp-out p = ! (pp-path b d) ∙ to-transp-out p

  ↓-pp-β : (q : fst (D b) d == d') → ↓-pp-out (↓-pp-in q) == q
  ↓-pp-β q =
    ↓-pp-out (↓-pp-in q)
               =⟨ idp ⟩
    ! (pp-path b d) ∙ to-transp-out (to-transp-in P (pp b) (pp-path b d ∙' q))
               =⟨ to-transp-β P (pp b) (pp-path b d ∙' q) |in-ctx (λ u → ! (pp-path b d) ∙ u) ⟩
    ! (pp-path b d) ∙ (pp-path b d ∙' q)
               =⟨ lem (pp-path b d) q ⟩
    q ∎
