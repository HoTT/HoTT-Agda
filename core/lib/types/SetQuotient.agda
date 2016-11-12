{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Relation
open import lib.NType2
open import lib.types.Pi

module lib.types.SetQuotient {i} {A : Type i} {j} where

postulate  -- HIT
  SetQuot : (R : Rel A j) → Type (lmax i j)

module _ {R : Rel A j} where

  postulate  -- HIT
    q[_] : (a : A) → SetQuot R
    quot-rel : {a₁ a₂ : A} → R a₁ a₂ → q[ a₁ ] == q[ a₂ ]
    SetQuot-level : is-set (SetQuot R)

  SetQuot-is-set = SetQuot-level

  module SetQuotElim {k} {P : SetQuot R → Type k}
    (p : (x : SetQuot R) → is-set (P x)) (q[_]* : (a : A) → P q[ a ])
    (rel* : ∀ {a₁ a₂} (r : R a₁ a₂) → q[ a₁ ]* == q[ a₂ ]* [ P ↓ quot-rel r ]) where

    postulate  -- HIT
      f : Π (SetQuot R) P
      q[_]-β : (a : A) → f q[ a ] ↦ q[ a ]*
    {-# REWRITE q[_]-β #-}

    postulate  -- HIT
      quot-rel-β : ∀ {a₁ a₂} (r : R a₁ a₂) → apd f (quot-rel r) == rel* r

  open SetQuotElim public using () renaming (f to SetQuot-elim)

  module SetQuotRec {k} {B : Type k} (p : is-set B)
    (q[_]* : A → B) (rel* : ∀ {a₁ a₂} (r : R a₁ a₂) → q[ a₁ ]* == q[ a₂ ]*) where

    private
      module M = SetQuotElim (λ x → p) q[_]* (λ {a₁ a₂} r → ↓-cst-in (rel* r))

    f : SetQuot R → B
    f = M.f

  open SetQuotRec public using () renaming (f to SetQuot-rec)

  -- If [R] is an equivalence relation, then [quot-rel] is an equivalence.

module _ {R : Rel A j}
  (R-is-prop : ∀ {a b} → is-prop (R a b))
  (R-is-refl : is-refl R) (R-is-sym : is-sym R)
  (R-is-trans : is-trans R) where

  private
    Q : Type (lmax i j)
    Q = SetQuot R

    R'-over-quot : Q → Q → hProp j
    R'-over-quot = SetQuot-rec (→-is-set $ hProp-is-set j)
      (λ a → SetQuot-rec (hProp-is-set j)
        (λ b → R a b , R-is-prop)
        (nType=-out ∘ lemma-a))
      (λ ra₁a₂ → λ= $ SetQuot-elim
        (λ _ → raise-level -1 $ hProp-is-set j _ _)
        (λ _ → nType=-out $ lemma-b ra₁a₂)
        (λ _ → prop-has-all-paths-↓ $ hProp-is-set j _ _))
      where
        abstract
          lemma-a : ∀ {a b₁ b₂} → R b₁ b₂ → R a b₁ == R a b₂
          lemma-a rb₁b₂ = ua $ equiv
            (λ rab₁ → R-is-trans rab₁ rb₁b₂)
            (λ rab₂ → R-is-trans rab₂ (R-is-sym rb₁b₂))
            (λ _ → prop-has-all-paths R-is-prop _ _)
            (λ _ → prop-has-all-paths R-is-prop _ _)

          lemma-b : ∀ {a₁ a₂ b} → R a₁ a₂ → R a₁ b == R a₂ b
          lemma-b ra₁a₂ = ua $ equiv
            (λ ra₁b → R-is-trans (R-is-sym ra₁a₂) ra₁b)
            (λ ra₂b → R-is-trans ra₁a₂ ra₂b)
            (λ _ → prop-has-all-paths R-is-prop _ _)
            (λ _ → prop-has-all-paths R-is-prop _ _)

    R-over-quot : Q → Q → Type j
    R-over-quot q₁ q₂ = fst (R'-over-quot q₁ q₂)

    abstract
      R-over-quot-is-prop : {q₁ q₂ : Q} → is-prop (R-over-quot q₁ q₂)
      R-over-quot-is-prop {q₁} {q₂} = snd (R'-over-quot q₁ q₂)

      R-over-quot-is-refl : (q : Q) → R-over-quot q q
      R-over-quot-is-refl = SetQuot-elim
        (λ q → raise-level -1 (R-over-quot-is-prop {q} {q}))
        (λ a → R-is-refl a)
        (λ _ → prop-has-all-paths-↓ R-is-prop)

      path-to-R-over-quot : {q₁ q₂ : Q} → q₁ == q₂ → R-over-quot q₁ q₂
      path-to-R-over-quot {q} idp = R-over-quot-is-refl q

  quot-rel-equiv : ∀ {a₁ a₂ : A} → R a₁ a₂ ≃ (q[ a₁ ] == q[ a₂ ])
  quot-rel-equiv {a₁} {a₂} = equiv
    quot-rel (path-to-R-over-quot {q[ a₁ ]} {q[ a₂ ]})
    (λ _ → prop-has-all-paths (SetQuot-is-set _ _) _ _)
    (λ _ → prop-has-all-paths R-is-prop _ _)
