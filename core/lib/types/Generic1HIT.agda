{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

{-
The generic nonrecursive higher inductive type with one point constructor and
one paths constructor.
-}

module lib.types.Generic1HIT {i j} (A : Type i) (B : Type j)
  (g h : B → A) where


{-
data T : Type where
  cc : A → T
  pp : (b : B) → cc (f' b) ≡ cc (g b)
-}
module _ where

  postulate  -- HIT
    T : Type (lmax i j)
    cc : A → T
    pp : (b : B) → cc (g b) == cc (h b)

  module Elim {k} {P : T → Type k} (cc* : (a : A) → P (cc a))
    (pp* : (b : B) → cc* (g b) == cc* (h b) [ P ↓ pp b ]) where

    postulate  -- HIT
      f : Π T P
      cc-β : ∀ a → f (cc a) ↦ cc* a
    {-# REWRITE cc-β #-}

    postulate  -- HIT
      pp-β : (b : B) → apd f (pp b) == pp* b

open Elim public using () renaming (f to elim)

module Rec {k} {C : Type k} (cc* : A → C)
  (pp* : (b : B) → cc* (g b) == cc* (h b)) where

  private module M = Elim cc* (λ b → ↓-cst-in (pp* b))

  f : T → C
  f = M.f

  pp-β : (b : B) → ap f (pp b) == pp* b
  pp-β b = apd=cst-in {f = f} (M.pp-β b)

module RecType {k} (C : A → Type k) (D : (b : B) → C (g b) ≃ C (h b)) where

  open Rec C (ua ∘ D) public

  coe-pp-β : (b : B) (d : C (g b)) → coe (ap f (pp b)) d == –> (D b) d
  coe-pp-β b d =
    coe (ap f (pp b)) d   =⟨ pp-β _ |in-ctx (λ u → coe u d) ⟩
    coe (ua (D b)) d      =⟨ coe-β (D b) d ⟩
    –> (D b) d            =∎

  -- Dependent path in [P] over [pp b]
  module _ {b : B} {d : C (g b)} {d' : C (h b)} where
    ↓-pp-in : –> (D b) d == d' → d == d' [ f ↓ pp b ]
    ↓-pp-in p = from-transp f (pp b) (coe-pp-β b d ∙' p)

    ↓-pp-out : d == d' [ f ↓ pp b ] → –> (D b) d == d'
    ↓-pp-out p = ! (coe-pp-β b d) ∙ to-transp p

    ↓-pp-β : (q : –> (D b) d == d') → ↓-pp-out (↓-pp-in q) == q
    ↓-pp-β q =
      ↓-pp-out (↓-pp-in q)
                        =⟨ idp ⟩
      ! (coe-pp-β b d) ∙ to-transp (from-transp f (pp b) (coe-pp-β b d ∙' q))
                 =⟨ to-transp-β f (pp b) (coe-pp-β b d ∙' q) |in-ctx (λ u → ! (coe-pp-β b d) ∙ u) ⟩
      ! (coe-pp-β b d) ∙ (coe-pp-β b d ∙' q)
                 =⟨ lem (coe-pp-β b d) q ⟩
      q =∎  where

        lem : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
          → ! p ∙ (p ∙' q) == q
        lem idp idp = idp
