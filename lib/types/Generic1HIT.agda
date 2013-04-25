{-# OPTIONS --without-K #-}

open import lib.Basics

{-
The generic nonrecursive higher inductive types with one point constructor and
one paths constructor.
-}

module lib.types.Generic1HIT {i j} (A : Type i) (B : Type j) (f g : B → A) where


{-
data Wg : Type where
  cc : A → Wg
  pp : (b : B) → cc (f b) ≡ cc (g b)
-}

private
  data #Wg : Type (max i j) where
    #cc : A → #Wg

Wg : Type _
Wg = #Wg

cc : A → Wg
cc = #cc

postulate  -- HIT
  pp : (b : B) → cc (f b) == cc (g b)

Wg-elim : ∀ {ℓ} {P : Wg → Type ℓ} (cc* : (a : A) → P (cc a))
  (pp* : (b : B) → cc* (f b) == cc* (g b) [ P ↓ pp b ])
  → ((w : Wg) → P w)
Wg-elim cc* pp* (#cc a) = cc* a

postulate  -- HIT
  pp-β : ∀ {ℓ} {P : Wg → Type ℓ} (cc* : (a : A) → P (cc a))
    (pp* : (b : B) → cc* (f b) == cc* (g b) [ P ↓ pp b ])
    → ((b : B) → apd (Wg-elim cc* pp*) (pp b) == pp* b)

Wg-rec : ∀ {ℓ} {P : Type ℓ} (cc* : A → P)
  (pp* : (b : B) → cc* (f b) == cc* (g b))
  → (Wg → P)
Wg-rec cc* pp* (#cc a) = cc* a

postulate  -- HIT
  pp-β' : ∀ {ℓ} {P : Type ℓ} (cc* : A → P)
    (pp* : (b : B) → cc* (f b) == cc* (g b))
    → ((b : B) → ap (Wg-rec cc* pp*) (pp b) == pp* b)

module _ {k} (C : A → Type k) (D : (b : B) → C (f b) ≃ C (g b)) where

  private
    P = Wg-rec C (ua ∘ D)

  pp-path : (b : B) (d : C (f b)) → coe (ap P (pp b)) d == –> (D b) d
  pp-path b d =
    coe (ap P (pp b)) d
              =⟨ pp-β' C (ua ∘ D) _ |in-ctx (λ u → coe u d) ⟩
    coe (ua (D b)) d
               =⟨ coe-β (D b) d ⟩
    –> (D b) d ∎

  -- Dependent path in [P] over [pp b]
  module _ {b : B} {d : C (f b)} {d' : C (g b)} where
    ↓-pp-in : (–> (D b) d == d' → d == d' [ P ↓ pp b ])
    ↓-pp-in p = from-transp P (pp b) (pp-path b d ∙' p)

    ↓-pp-out : (d == d' [ P ↓ pp b ] → –> (D b) d == d')
    ↓-pp-out p = ! (pp-path b d) ∙ to-transp p

    ↓-pp-β : (q : –> (D b) d == d') → ↓-pp-out (↓-pp-in q) == q
    ↓-pp-β q =
      ↓-pp-out (↓-pp-in q)
                        =⟨ idp ⟩
      ! (pp-path b d) ∙ to-transp (from-transp P (pp b) (pp-path b d ∙' q))
                 =⟨ to-transp-β P (pp b) (pp-path b d ∙' q) |in-ctx (λ u → ! (pp-path b d) ∙ u) ⟩
      ! (pp-path b d) ∙ (pp-path b d ∙' q)
                 =⟨ lem (pp-path b d) q ⟩
      q ∎  where

        lem : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
          → ! p ∙ (p ∙' q) == q
        lem idp idp = idp
