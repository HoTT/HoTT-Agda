{-# OPTIONS --without-K #-}

open import HoTT hiding (_::_)

module algebra.ReducedWord {i} (A : Type i) (dec : has-dec-eq A) where

  open import algebra.Word A

  is-reduced : Word → Type i
  is-reduced nil                 = Lift ⊤
  is-reduced (x    :: nil)       = Lift ⊤
  is-reduced (x    :: y    :: w) = is-reduced (y :: w)
  is-reduced (x    :: y inv:: w) = (x ≠ y) × is-reduced (y inv:: w)
  is-reduced (x inv:: nil)       = Lift Unit
  is-reduced (x inv:: y    :: w) = (x ≠ y) × is-reduced (y :: w)
  is-reduced (x inv:: y inv:: w) = is-reduced (y inv:: w)

  ReducedWord : Type i
  ReducedWord = Σ Word is-reduced

  -- Everything is a set.

  A-is-set : is-set A
  A-is-set = dec-eq-is-set dec

  Word-has-dec-eq : has-dec-eq (Word)
  Word-has-dec-eq nil nil = inl idp
  Word-has-dec-eq nil         (x    :: w) = inr (lower ∘ Word=-out)
  Word-has-dec-eq nil         (x inv:: w) = inr (lower ∘ Word=-out)
  Word-has-dec-eq (x    :: v) nil         = inr (lower ∘ Word=-out)
  Word-has-dec-eq (x    :: v) (y    :: w) with (dec x y)
  Word-has-dec-eq (x    :: v) (y    :: w) | inl x=y with (Word-has-dec-eq v w)
  Word-has-dec-eq (x    :: v) (y    :: w) | inl x=y | inl v=w = inl (Word=-in (x=y , v=w))
  Word-has-dec-eq (x    :: v) (y    :: w) | inl x=y | inr v≠w = inr (v≠w ∘ Word-snd=)
  Word-has-dec-eq (x    :: v) (y    :: w) | inr x≠y = inr (x≠y ∘ Word-fst=)
  Word-has-dec-eq (x    :: v) (y inv:: w) = inr (lower ∘ Word=-out)
  Word-has-dec-eq (x inv:: v) nil         = inr (lower ∘ Word=-out)
  Word-has-dec-eq (x inv:: v) (y    :: w) = inr (lower ∘ Word=-out)
  Word-has-dec-eq (x inv:: v) (y inv:: w) with (dec x y)
  Word-has-dec-eq (x inv:: v) (y inv:: w) | inl x=y with (Word-has-dec-eq v w)
  Word-has-dec-eq (x inv:: v) (y inv:: w) | inl x=y | inl v=w = inl (Word=-in (x=y , v=w))
  Word-has-dec-eq (x inv:: v) (y inv:: w) | inl x=y | inr v≠w = inr (v≠w ∘ Word-snd=')
  Word-has-dec-eq (x inv:: v) (y inv:: w) | inr x≠y = inr (x≠y ∘ Word-fst=')

  Word-is-set : is-set Word
  Word-is-set = dec-eq-is-set Word-has-dec-eq

  is-reduced-is-prop : (w : Word) → is-prop (is-reduced w)
  is-reduced-is-prop nil                 = Lift-level Unit-is-prop
  is-reduced-is-prop (x    :: nil)       = Lift-level Unit-is-prop
  is-reduced-is-prop (x    :: y    :: w) = is-reduced-is-prop (y :: w)
  is-reduced-is-prop (x    :: y inv:: w) =
    ×-level (Π-is-prop (λ _ → λ ())) (is-reduced-is-prop (y inv:: w))
  is-reduced-is-prop (x inv:: nil)       = Lift-level Unit-is-prop
  is-reduced-is-prop (x inv:: y    :: w) =
    ×-level (Π-is-prop (λ _ → λ ())) (is-reduced-is-prop (y :: w))
  is-reduced-is-prop (x inv:: y inv:: w) = is-reduced-is-prop (y inv:: w)

  ReducedWord-is-set : is-set ReducedWord
  ReducedWord-is-set = Subtype-level Word-is-set is-reduced-is-prop

  ReducedWord= : ReducedWord → ReducedWord → Type i
  ReducedWord= = Subtype=

  ReducedWord=-in : {x y : ReducedWord} → ReducedWord= x y → x == y
  ReducedWord=-in {x} {y} = Subtype=-in (is-reduced-is-prop (fst y))
