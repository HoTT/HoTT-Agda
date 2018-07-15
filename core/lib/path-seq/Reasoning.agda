{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Equivalence
open import lib.PathGroupoid
open import lib.NType
open import lib.Univalence
open import lib.path-seq.Concat
open import lib.path-seq.Split

module lib.path-seq.Reasoning where

module _ {i} {A : Type i} where
  infix 30 _=↯=_
  _=↯=_ : {a a' : A} → a =-= a' → a =-= a' → Type i
  _=↯=_ s t = (↯ s) == (↯ t)

  record _=ₛ-free-end_ {a aₛ' aₜ' : A} (s : a =-= aₛ') (t : a =-= aₜ') : Type i where
    constructor =ₛ-free-end-intro
    field
      end-matches : aₛ' == aₜ'
      path : (↯ s) ∙' end-matches == (↯ t)

  instance
    =ₛ-free-end-refl : {a a' : A} {s : a =-= a'} → s =ₛ-free-end s
    =ₛ-free-end-refl = record { end-matches = idp; path = idp }

  record _=ₛ-free-start_ {aₛ aₜ a' : A} (s : aₛ =-= a') (t : aₜ =-= a') : Type i where
    constructor =ₛ-free-start-intro
    field
      start-matches : aₛ == aₜ
      path : (↯ s) == start-matches ∙ (↯ t)

  instance
    =ₛ-free-start-refl : {a a' : A} {s : a =-= a'} → s =ₛ-free-start s
    =ₛ-free-start-refl = record { start-matches = idp; path = idp }

module _ {i} {A : Type i} {a a' : A} where

  =-=ₛ-equiv : (s t : a =-= a') → (s =↯= t) ≃ (s =ₛ t)
  =-=ₛ-equiv s t = equiv =ₛ-in =ₛ-out (λ _ → idp) (λ _ → idp)

  =ₛ-level : {s t : a =-= a'} {n : ℕ₋₂}
    → has-level (S (S n)) A → has-level n (s =ₛ t)
  =ₛ-level {s} {t} {n} A-level =
    transport (has-level n) (ua (=-=ₛ-equiv s t)) $
    has-level-apply (has-level-apply A-level _ _) _ _

  !ₛ : {s t : a =-= a'} → s =ₛ t → t =ₛ s
  !ₛ (=ₛ-in p) = =ₛ-in (! p)

  _∙ₛ_ : {s t u : a =-= a'} → s =ₛ t → t =ₛ u → s =ₛ u
  _∙ₛ_ (=ₛ-in p) (=ₛ-in q) = =ₛ-in (p ∙ q)

  expand : (s : a =-= a') → ↯ s ◃∎ =ₛ s
  expand s = =ₛ-in idp

  contract : {s : a =-= a'} → s =ₛ ↯ s ◃∎
  contract = =ₛ-in idp

  abstract
    {-
      Note: While this enables more succinct chains of equations in comparison to
      chains using _=↯=⟨_&_&_&_⟩_ (since it avoids having to spell out the target
      subsequence), it is also results in significantly (~ one order of magnitude)
      slower type checking. Therefore, this function should only be used for
      developing new proofs, not to simplify old proofs.
    -}
    infixr 10 _=ₛ⟨_&_&_&_⟩_
    _=ₛ⟨_&_&_&_⟩_ : (s : a =-= a') {t u : a =-= a'}
      → (m n o : ℕ)
      → {{init-matches : take m s =ₛ-free-end (take m t)}}
      → {{tail-matches : drop n (drop m s) =ₛ-free-start (drop o (drop m t))}}
      → (path : ↯ (take n (drop m s)) ∙' _=ₛ-free-start_.start-matches tail-matches ==
                _=ₛ-free-end_.end-matches init-matches ∙ ↯ (take o (drop m t)))
      → t =ₛ u
      → s =ₛ u
    _=ₛ⟨_&_&_&_⟩_ s {t} {u} m n o {{init-matches}} {{tail-matches}} path q =
      =ₛ-in $
        ↯ s
          =⟨ =ₛ-out (take-drop-split m s) ⟩
        ↯ (take m s) ∙ ↯ (drop m s)
          =⟨ ap (↯ (take m s) ∙_) (=ₛ-out (take-drop-split n (drop m s))) ⟩
        ↯ (take m s) ∙ ↯ (take n (drop m s)) ∙ ↯ (drop n (drop m s))
          =⟨ ap (λ w → ↯ (take m s) ∙ ↯ (take n (drop m s)) ∙ w) tail-matches.path ⟩
        ↯ (take m s) ∙ ↯ (take n (drop m s)) ∙ tail-matches.start-matches ∙ ↯ (drop o (drop m t))
          =⟨ ap (λ w → ↯ (take m s) ∙ w) (! (∙-assoc (↯ (take n (drop m s))) tail-matches.start-matches (↯ (drop o (drop m t))))) ⟩
        ↯ (take m s) ∙ (↯ (take n (drop m s)) ∙ tail-matches.start-matches) ∙ ↯ (drop o (drop m t))
          =⟨ ap (λ w → ↯ (take m s) ∙ w ∙ ↯ (drop o (drop m t)))
                (∙=∙' (↯ (take n (drop m s))) tail-matches.start-matches ∙ path) ⟩
        ↯ (take m s) ∙ (init-matches.end-matches ∙ ↯ (take o (drop m t))) ∙ ↯ (drop o (drop m t))
          =⟨ ap (λ w → ↯ (take m s) ∙ w) (∙-assoc init-matches.end-matches (↯ (take o (drop m t))) (↯ (drop o (drop m t)))) ⟩
        ↯ (take m s) ∙ init-matches.end-matches ∙ ↯ (take o (drop m t)) ∙ ↯ (drop o (drop m t))
          =⟨ ! (∙-assoc (↯ (take m s)) init-matches.end-matches (↯ (take o (drop m t)) ∙ ↯ (drop o (drop m t)))) ⟩
        (↯ (take m s) ∙ init-matches.end-matches) ∙ ↯ (take o (drop m t)) ∙ ↯ (drop o (drop m t))
          =⟨ ap (λ w → w ∙ ↯ (take o (drop m t)) ∙ ↯ (drop o (drop m t)))
                (∙=∙' (↯ (take m s)) init-matches.end-matches ∙ init-matches.path) ⟩
        ↯ (take m t) ∙ ↯ (take o (drop m t)) ∙ ↯ (drop o (drop m t))
          =⟨ ! (ap (↯ (take m t) ∙_) (=ₛ-out (take-drop-split o (drop m t)))) ⟩
        ↯ (take m t) ∙ ↯ (drop m t)
          =⟨ ! (=ₛ-out (take-drop-split m t)) ⟩
        ↯ t
          =⟨ =ₛ-out q ⟩
        ↯ u =∎
      where
      module init-matches = _=ₛ-free-end_ init-matches
      module tail-matches = _=ₛ-free-start_ tail-matches

    infixr 10 _=ₛ⟨_⟩_
    _=ₛ⟨_⟩_ : (s : a =-= a') {t u : a =-= a'}
      → s =ₛ t
      → t =ₛ u
      → s =ₛ u
    _=ₛ⟨_⟩_ _ p q = p ∙ₛ q

  infix 15 _∎ₛ
  _∎ₛ : (s : a =-= a') → s =ₛ s
  _∎ₛ _ = =ₛ-in idp

module _ {i} {A : Type i} where

  abstract
    private
      infixr 10 _=↯=⟨_&_&_&_⟩_
      _=↯=⟨_&_&_&_⟩_ : {a a' : A} {q : a == a'}
        → (s : a =-= a')
        → (n : ℕ) (m : ℕ)
        → (t : point-from-start n s =-= point-from-start m (drop n s))
        → take m (drop n s) =↯= t
        → ↯ (take n s ∙∙ t ∙∙ drop m (drop n s)) == q
        → ↯ s == q
      _=↯=⟨_&_&_&_⟩_ {a} {a'} {q} s n m t p p' =
        ↯ s
          =⟨ =ₛ-out (take-drop-split n s) ⟩
        ↯ (take n s) ∙ ↯ (drop n s)
          =⟨ ap (↯ (take n s) ∙_) (=ₛ-out (take-drop-split m (drop n s))) ⟩
        ↯ (take n s) ∙ ↯ (take m (drop n s)) ∙ ↯ (drop m (drop n s))
          =⟨ ap (λ v → ↯ (take n s) ∙ v ∙ ↯ (drop m (drop n s))) p ⟩
        ↯ (take n s) ∙ ↯ t ∙ ↯ (drop m (drop n s))
          =⟨ ap (λ v → ↯ (take n s) ∙ v) (! (↯-∙∙ t (drop m (drop n s)))) ⟩
        ↯ (take n s) ∙ ↯ (t ∙∙ drop m (drop n s))
          =⟨ ! (↯-∙∙ (take n s) (t ∙∙ drop m (drop n s))) ⟩
        ↯ (take n s ∙∙ t ∙∙ drop m (drop n s))
          =⟨ p' ⟩
        q =∎

    infixr 10 _=ₛ⟨id⟩_
    _=ₛ⟨id⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → s =ₛ u
      → s =ₛ u
    _=ₛ⟨id⟩_ s e = e

    infixr 10 _=ₛ⟨_&_&_⟩_
    _=ₛ⟨_&_&_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → (m n : ℕ)
      → {r : point-from-start m s =-= point-from-start n (drop m s)}
      → take n (drop m s) =ₛ r
      → take m s ∙∙ r ∙∙ drop n (drop m s) =ₛ u
      → s =ₛ u
    _=ₛ⟨_&_&_⟩_ s m n {r} p p' = =ₛ-in (s =↯=⟨ m & n & r & =ₛ-out p ⟩ =ₛ-out p')

    infixr 10 _=ₛ₁⟨_&_&_⟩_
    _=ₛ₁⟨_&_&_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → (m n : ℕ)
      → {r : point-from-start m s == point-from-start n (drop m s)}
      → ↯ (take n (drop m s)) == r
      → take m s ∙∙ r ◃∙ drop n (drop m s) =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_&_&_⟩_ s m n {r} p p' = s =ₛ⟨ m & n & =ₛ-in {t = r ◃∎} p ⟩ p'

    infixr 10 _=ₛ₁⟨_⟩_
    _=ₛ₁⟨_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → {r : a == a'}
      → ↯ s == r
      → r ◃∎ =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_⟩_ s {r} p p' = =ₛ-in p ∙ₛ p'
