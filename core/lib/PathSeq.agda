{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Equivalence
open import lib.Function
open import lib.NType
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Univalence

module lib.PathSeq where

{-
This is a library on reified equational reasoning.
When you write the following (with the usual equational reasoning combinators):

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

it just creates the concatenation of [p], [q], [r] and [s] and there is no way
to say “remove the last step to get the path from [a] to [d]”.
With the present library you would write:

  t : PathSeq a e
  t = a =⟪ p ⟫
      b =⟪ q ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e ∎∎

Then the actual path from [a] to [e] is [↯ t], and you can strip any number
of steps from the beginning or the end:

  ↯ t !2
-}


module _ {i} {A : Type i} where
  infix 15 _∎∎
  infixr 10 _=⟪_⟫_
  infixr 10 _=⟪idp⟫_

  _∎∎ : (a : A) → a =-= a
  _∎∎ _ = []

  _=⟪_⟫_ : (a : A) {a' a'' : A} (p : a == a') (s : a' =-= a'') → a =-= a''
  _=⟪_⟫_ _ p s = p ◃∙ s

  _=⟪idp⟫_ : (a : A) {a' : A} (s : a =-= a') → a =-= a'
  a =⟪idp⟫ s = s

module _ {i} {A : Type i} where


  {- concatenation -}
  infixr 80 _∙∙_
  _∙∙_ : {a a' a'' : A}
    → a =-= a' → a' =-= a'' → a =-= a''
  _∙∙_ [] t = t
  _∙∙_ (p ◃∙ s) t = p ◃∙ (s ∙∙ t)

  ∙∙-assoc : {a a' a'' a''' : A}
    (s : a =-= a') (t : a' =-= a'') (u : a'' =-= a''')
    → (s ∙∙ t) ∙∙ u == s ∙∙ (t ∙∙ u)
  ∙∙-assoc [] t u = idp
  ∙∙-assoc (p ◃∙ s) t u = ap (p ◃∙_) (∙∙-assoc s t u)

  ∙∙-unit-r : {a a' : A} (s : a =-= a')
    → s ∙∙ (a' ∎∎) == s
  ∙∙-unit-r [] = idp
  ∙∙-unit-r (p ◃∙ s) = ap (p ◃∙_) (∙∙-unit-r s)

  infixl 80 _∙▹_
  _∙▹_ : {a a' a'' : A}
    → a =-= a' → a' == a'' → a =-= a''
  _∙▹_ {a} {a'} {a''} s p = s ∙∙ (p ◃∙ [])

  seq-! : {a a' : A} → a =-= a' → a' =-= a
  seq-! [] = []
  seq-! (p ◃∙ s) = seq-! s ∙▹ ! p

  ↯-∙∙ : {a a' a'' : A} (s : a =-= a') (t : a' =-= a'')
    → ↯ (s ∙∙ t) == ↯ s ∙ ↯ t
  ↯-∙∙ [] t = idp
  ↯-∙∙ (p ◃∙ []) [] = ! (∙-unit-r p)
  ↯-∙∙ (p ◃∙ []) (p' ◃∙ t) = idp
  ↯-∙∙ (p ◃∙ s@(_ ◃∙ _)) t =
    ap (λ y → p ∙ y) (↯-∙∙ s t) ∙
    ! (∙-assoc p (↯ s) (↯ t))

  infix 30 _=↯=_
  _=↯=_ : {a a' : A} → a =-= a' → a =-= a' → Type i
  _=↯=_ s t = (↯ s) == (↯ t)

  point-from-start : (n : ℕ) {a a' : A} (s : a =-= a') → A
  point-from-start O {a} s = a
  point-from-start (S n) {a = a} [] = a
  point-from-start (S n) (p ◃∙ s) = point-from-start n s

  _-! : (n : ℕ) {a a' : A} (s : a =-= a') → point-from-start n s =-= a'
  (O -!) s = s
  (S n -!) [] = []
  (S n -!) (p ◃∙ s) = (n -!) s

  private
    last1 : {a a' : A} (s : a =-= a') → A
    last1 {a = a} [] = a
    last1 {a = a} (p ◃∙ []) = a
    last1 (p ◃∙ s@(_ ◃∙ _)) = last1 s

    strip : {a a' : A} (s : a =-= a') → a =-= last1 s
    strip [] = []
    strip (p ◃∙ []) = []
    strip (p ◃∙ s@(_ ◃∙ _)) = p ◃∙ strip s

    point-from-end : (n : ℕ) {a a' : A} (s : a =-= a') → A
    point-from-end O {a} {a'} s = a'
    point-from-end (S n) s = point-from-end n (strip s)

  !- : (n : ℕ) {a a' : A} (s : a =-= a') → a =-= point-from-end n s
  !- O s = s
  !- (S n) s = !- n (strip s)

  _-# : (n : ℕ) {a a' : A} (s : a =-= a') → a =-= point-from-start n s
  (O -#) s = []
  (S n -#) [] = []
  (S n -#) (p ◃∙ s) = p ◃∙ (n -#) s

  abstract
    ∙∙-#-! : {a a' : A} (s : a =-= a') (n : ℕ)
      → s == (n -#) s ∙∙ (n -!) s
    ∙∙-#-! s O = idp
    ∙∙-#-! [] (S n) = idp
    ∙∙-#-! (p ◃∙ s) (S n) = ap (λ v → p ◃∙ v) (∙∙-#-! s n)

    ↯-#-! : {a a' : A} (s : a =-= a') (n : ℕ)
      → ↯ s == ↯ ((n -#) s) ∙ ↯ ((n -!) s)
    ↯-#-! s n =
      ↯ s
        =⟨ ap ↯ (∙∙-#-! s n) ⟩
      ↯ ((n -#) s ∙∙ (n -!) s)
        =⟨ ↯-∙∙ ((n -#) s) ((n -!) s) ⟩
      ↯ ((n -#) s) ∙ ↯ ((n -!) s) =∎

  private
    split : {a a' : A} (s : a =-= a')
      → Σ A (λ a'' → Σ (a =-= a'') (λ _ → a'' == a'))
    split {a = a} [] = (a , ([] , idp))
    split {a = a} (p ◃∙ []) = (a , ([] , p))
    split (p ◃∙ s@(_ ◃∙ _)) =
      let (a'' , (t , q)) = split s
      in (a'' , (p ◃∙ t) , q)

    point-from-end' : (n : ℕ) {a a' : A} (s : a =-= a') → A
    point-from-end' n {a = a} [] = a
    point-from-end' O (p ◃∙ s) = point-from-end' O s
    point-from-end' (S n) (p ◃∙ s) = point-from-end' n (fst (snd (split (p ◃∙ s))))

  #- : (n : ℕ) {a a' : A} (s : a =-= a') → point-from-end' n s =-= a'
  #- n [] = []
  #- O (p ◃∙ s) = #- O s
  #- (S n) (p ◃∙ s) = let (a' , (t , q)) = split (p ◃∙ s) in #- n t ∙▹ q

  infix 120 _!0 _!1 _!2 _!3 _!4 _!5
  _!0 = !- 0
  _!1 = !- 1
  _!2 = !- 2
  _!3 = !- 3
  _!4 = !- 4
  _!5 = !- 5

  0! = 0 -!
  1! = 1 -!
  2! = 2 -!
  3! = 3 -!
  4! = 4 -!
  5! = 5 -!

  infix 120 _#0 _#1 _#2 _#3 _#4 _#5
  _#0 = #- 0
  _#1 = #- 1
  _#2 = #- 2
  _#3 = #- 3
  _#4 = #- 4
  _#5 = #- 5

  0# = 0 -#
  1# = 1 -#
  2# = 2 -#
  3# = 3 -#
  4# = 4 -#
  5# = 5 -#

module _ {i} {A : Type i} where
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
      → {{init-matches : ((m -#) s) =ₛ-free-end ((m -#) t)}}
      → {{tail-matches : ((n -!) ((m -!) s)) =ₛ-free-start ((o -!) ((m -!) t))}}
      → (path : ↯ ((n -#) ((m -!) s)) ∙' _=ₛ-free-start_.start-matches tail-matches ==
                _=ₛ-free-end_.end-matches init-matches ∙ ↯ ((o -#) ((m -!) t)))
      → t =ₛ u
      → s =ₛ u
    _=ₛ⟨_&_&_&_⟩_ s {t} {u} m n o {{init-matches}} {{tail-matches}} path q =
      =ₛ-in $
        ↯ s
          =⟨ ↯-#-! s m ⟩
        ↯ ((m -#) s) ∙ ↯ ((m -!) s)
          =⟨ ap (↯ ((m -#) s) ∙_) (↯-#-! ((m -!) s) n) ⟩
        ↯ ((m -#) s) ∙ ↯ ((n -#) ((m -!) s)) ∙ ↯ ((n -!) ((m -!) s))
          =⟨ ap (λ w → ↯ ((m -#) s) ∙ ↯ ((n -#) ((m -!) s)) ∙ w) tail-matches.path ⟩
        ↯ ((m -#) s) ∙ ↯ ((n -#) ((m -!) s)) ∙ tail-matches.start-matches ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ap (λ w → ↯ ((m -#) s) ∙ w) (! (∙-assoc (↯ ((n -#) ((m -!) s))) tail-matches.start-matches (↯ ((o -!) ((m -!) t))))) ⟩
        ↯ ((m -#) s) ∙ (↯ ((n -#) ((m -!) s)) ∙ tail-matches.start-matches) ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ap (λ w → ↯ ((m -#) s) ∙ w ∙ ↯ ((o -!) ((m -!) t)))
                (∙=∙' (↯ ((n -#) ((m -!) s))) tail-matches.start-matches ∙ path) ⟩
        ↯ ((m -#) s) ∙ (init-matches.end-matches ∙ ↯ ((o -#) ((m -!) t))) ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ap (λ w → ↯ ((m -#) s) ∙ w) (∙-assoc init-matches.end-matches (↯ ((o -#) ((m -!) t))) (↯ ((o -!) ((m -!) t)))) ⟩
        ↯ ((m -#) s) ∙ init-matches.end-matches ∙ ↯ ((o -#) ((m -!) t)) ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ! (∙-assoc (↯ ((m -#) s)) init-matches.end-matches (↯ ((o -#) ((m -!) t)) ∙ ↯ ((o -!) ((m -!) t)))) ⟩
        (↯ ((m -#) s) ∙ init-matches.end-matches) ∙ ↯ ((o -#) ((m -!) t)) ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ap (λ w → w ∙ ↯ ((o -#) ((m -!) t)) ∙ ↯ ((o -!) ((m -!) t)))
                (∙=∙' (↯ ((m -#) s)) init-matches.end-matches ∙ init-matches.path) ⟩
        ↯ ((m -#) t) ∙ ↯ ((o -#) ((m -!) t)) ∙ ↯ ((o -!) ((m -!) t))
          =⟨ ! (ap (↯ ((m -#) t) ∙_) (↯-#-! ((m -!) t) o)) ⟩
        ↯ ((m -#) t) ∙ ↯ ((m -!) t)
          =⟨ ! (↯-#-! t m) ⟩
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
        → (t : point-from-start n s =-= point-from-start m ((n -!) s))
        → (m -#) ((n -!) s) =↯= t
        → ↯ (((n -#) s) ∙∙ t ∙∙ ((m -!) ((n -!) s))) == q
        → (↯ s) == q
      _=↯=⟨_&_&_&_⟩_ {a} {a'} {q} s n m t p p' =
        ↯ s
          =⟨ ↯-#-! s n ⟩
        ↯ ((n -#) s) ∙ ↯ ((n -!) s)
          =⟨ ap (↯ ((n -#) s) ∙_) (↯-#-! ((n -!) s) m) ⟩
        ↯ ((n -#) s) ∙ ↯ ((m -#) ((n -!) s)) ∙ ↯ ((m -!) ((n -!) s))
          =⟨ ap (λ v → ↯ ((n -#) s) ∙ v ∙ ↯ ((m -!) ((n -!) s))) p ⟩
        ↯ ((n -#) s) ∙ (↯ t) ∙ ↯ ((m -!) ((n -!) s))
          =⟨ ap (λ v → ↯ ((n -#) s) ∙ v) (! (↯-∙∙ t ((m -!) ((n -!) s)))) ⟩
        ↯ ((n -#) s) ∙ ↯ (t ∙∙ (m -!) ((n -!) s))
          =⟨ ! (↯-∙∙ ((n -#) s) (t ∙∙ (m -!) ((n -!) s))) ⟩
        ↯ ((n -#) s ∙∙ t ∙∙ (m -!) ((n -!) s))
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
      → {r : point-from-start m s =-= point-from-start n ((m -!) s)}
      → (n -#) ((m -!) s) =ₛ r
      → (m -#) s ∙∙ r ∙∙ (n -!) ((m -!) s) =ₛ u
      → s =ₛ u
    _=ₛ⟨_&_&_⟩_ s m n {r} p p' = =ₛ-in (s =↯=⟨ m & n & r & =ₛ-out p ⟩ =ₛ-out p')

    infixr 10 _=ₛ₁⟨_&_&_⟩_
    _=ₛ₁⟨_&_&_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → (m n : ℕ)
      → {r : point-from-start m s == point-from-start n ((m -!) s)}
      → ↯ ((n -#) ((m -!) s)) == r
      → (m -#) s ∙∙ r ◃∙ (n -!) ((m -!) s) =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_&_&_⟩_ s m n {r} p p' = s =ₛ⟨ m & n & =ₛ-in {t = r ◃∎} p ⟩ p'

    infixr 10 _=ₛ₁⟨_⟩_
    _=ₛ₁⟨_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → {r : a == a'}
      → ↯ s == r
      → r ◃∎ =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_⟩_ s {r} p p' = =ₛ-in p ∙ₛ p'

module _ {i} {A : Type i} where
  {-
  The order of the arguments p, q, r follows the occurrences
  of these variables in the output type
  -}

  pre-rotate-in : {a a' a'' : A} {q : a' =-= a''} {p : a == a'} {r : a =-= a''}
    → p ◃∙ q =ₛ r
    → q =ₛ ! p ◃∙ r
  pre-rotate-in {q = q} {p = idp} {r = r} e =
    q
      =ₛ⟨ =ₛ-in (! (↯-∙∙ (idp ◃∎) q)) ⟩
    idp ◃∙ q
      =ₛ⟨ e ⟩
    r
      =ₛ⟨ =ₛ-in (! (↯-∙∙ (idp ◃∎) r)) ⟩
    idp ◃∙ r ∎ₛ

  pre-rotate'-in : {a a' a'' : A} {p : a == a'} {r : a =-= a''} {q : a' =-= a''}
    → r =ₛ p ◃∙ q
    → ! p ◃∙ r =ₛ q
  pre-rotate'-in e =
    !ₛ (pre-rotate-in (!ₛ e))

  pre-rotate-seq-in : {a a' a'' : A} {q : a' =-= a''} {p : a =-= a'} {r : a =-= a''}
    → p ∙∙ q =ₛ r
    → q =ₛ seq-! p ∙∙ r
  pre-rotate-seq-in {q = q} {p = []} {r = r} e = e
  pre-rotate-seq-in {q = q} {p = p ◃∙ s} {r = r} e =
    q
      =ₛ⟨ pre-rotate-seq-in {q = q} {p = s} {r = ! p ◃∙ r} (pre-rotate-in e) ⟩
    seq-! s ∙∙ ! p ◃∙ r
      =ₛ⟨ =ₛ-in (ap ↯ (! (∙∙-assoc (seq-! s) (! p ◃∎) r))) ⟩
    seq-! (p ◃∙ s) ∙∙ r ∎ₛ

  pre-rotate'-seq-in : {a a' a'' : A} {p : a =-= a'} {r : a =-= a''} {q : a' =-= a''}
    → r =ₛ p ∙∙ q
    → seq-! p ∙∙ r =ₛ q
  pre-rotate'-seq-in {p = p} {r = r} {q = q} e =
    !ₛ (pre-rotate-seq-in {q = q} {p} {r} (!ₛ e))

  post-rotate'-in : {a a' a'' : A}
    → {r : a =-= a''} {q : a' == a''} {p : a =-= a'}
    → r =ₛ p ∙▹ q
    → r ∙▹ ! q =ₛ p
  post-rotate'-in {r = r} {q = idp} {p = p} e =
    r ∙▹ idp
      =ₛ⟨ =ₛ-in (↯-∙∙ r (idp ◃∎) ∙ ∙-unit-r (↯ r)) ⟩
    r
      =ₛ⟨ e ⟩
    p ∙▹ idp
      =ₛ⟨ =ₛ-in (↯-∙∙ p (idp ◃∎) ∙ ∙-unit-r (↯ p)) ⟩
    p ∎ₛ

  post-rotate-in : {a a' a'' : A}
    → {p : a =-= a'} {r : a =-= a''} {q : a' == a''}
    → p ∙▹ q =ₛ r
    → p =ₛ r ∙▹ ! q
  post-rotate-in {p = p} {r = r} {q = q} e =
    !ₛ (post-rotate'-in (!ₛ e))

  post-rotate'-seq-in : {a a' a'' : A}
    → {r : a =-= a''} {q : a' =-= a''} {p : a =-= a'}
    → r =ₛ p ∙∙ q
    → r ∙∙ (seq-! q) =ₛ p
  post-rotate'-seq-in {r = r} {q = []} {p = p} e =
    r ∙∙ []
      =ₛ⟨ =ₛ-in (ap ↯ (∙∙-unit-r r)) ⟩
    r
      =ₛ⟨ e ⟩
    p ∙∙ []
      =ₛ⟨ =ₛ-in (ap ↯ (∙∙-unit-r p)) ⟩
    p ∎ₛ
  post-rotate'-seq-in {r = r} {q = q ◃∙ s} {p = p} e =
    r ∙∙ (seq-! s ∙▹ ! q)
      =ₛ⟨ =ₛ-in (ap ↯ (! (∙∙-assoc r (seq-! s) (! q ◃∎)))) ⟩
    (r ∙∙ seq-! s) ∙▹ ! q
      =ₛ⟨ post-rotate'-in {r = r ∙∙ seq-! s} {q = q} {p = p} $
          post-rotate'-seq-in {r = r} {s} {p ∙▹ q} $
          r
            =ₛ⟨ e ⟩
          p ∙∙ (q ◃∙ s)
            =ₛ⟨ =ₛ-in (ap ↯ (! (∙∙-assoc p (q ◃∎) s))) ⟩
          (p ∙▹ q) ∙∙ s ∎ₛ
        ⟩
    p ∎ₛ

  post-rotate-seq-in : {a a' a'' : A}
    → {p : a =-= a'} {r : a =-= a''} {q : a' =-= a''}
    → p ∙∙ q =ₛ r
    → p =ₛ r ∙∙ (seq-! q)
  post-rotate-seq-in {p = p} {r = r} {q = q} e =
    !ₛ (post-rotate'-seq-in {r = r} {q = q} {p = p} (!ₛ e))

module _ {i} {A : Type i} where

  !-∙-seq : {a a' : A} (s : a =-= a')
    → ! (↯ s) ◃∎ =ₛ seq-! s
  !-∙-seq [] = =ₛ-in idp
  !-∙-seq (p ◃∙ s) =
    ! (↯ (p ◃∙ s)) ◃∎
      =ₛ₁⟨ ap ! (↯-∙∙ (p ◃∎) s) ⟩
    ! (p ∙ ↯ s) ◃∎
      =ₛ⟨ =ₛ-in {t = ! (↯ s) ◃∙ ! p ◃∎} (!-∙ p (↯ s)) ⟩
    ! (↯ s) ◃∙ ! p ◃∎
      =ₛ⟨ 0 & 1 & !-∙-seq s ⟩
    seq-! s ∙▹ ! p ∎ₛ

  ∙-!-seq : {a a' : A} (s : a =-= a')
    → seq-! s =ₛ ! (↯ s) ◃∎
  ∙-!-seq s = !ₛ (!-∙-seq s)

  !-=ₛ : {a a' : A} {s t : a =-= a'} (e : s =ₛ t)
    → seq-! s =ₛ seq-! t
  !-=ₛ {s = s} {t = t} e =
    seq-! s
      =ₛ⟨ ∙-!-seq s ⟩
    ! (↯ s) ◃∎
      =ₛ₁⟨ ap ! (=ₛ-out e) ⟩
    ! (↯ t) ◃∎
      =ₛ⟨ !-∙-seq t ⟩
    seq-! t ∎ₛ

  seq-!-inv-l : {a a' : A} (s : a =-= a')
    → seq-! s ∙∙ s =ₛ []
  seq-!-inv-l s = =ₛ-in $
    ↯ (seq-! s ∙∙ s)
      =⟨ ↯-∙∙ (seq-! s) s ⟩
    ↯ (seq-! s) ∙ ↯ s
      =⟨ ap (_∙ ↯ s) (=ₛ-out (∙-!-seq s)) ⟩
    ! (↯ s) ∙ ↯ s
      =⟨ !-inv-l (↯ s) ⟩
    idp =∎

  seq-!-inv-r : {a a' : A} (s : a =-= a')
    → s ∙∙ seq-! s =ₛ []
  seq-!-inv-r s = =ₛ-in $
    ↯ (s ∙∙ seq-! s)
      =⟨ ↯-∙∙ s (seq-! s) ⟩
    ↯ s ∙ ↯ (seq-! s)
      =⟨ ap (↯ s ∙_) (=ₛ-out (∙-!-seq s)) ⟩
    ↯ s ∙ ! (↯ s)
      =⟨ !-inv-r (↯ s) ⟩
    idp =∎

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-seq : {a a' : A} → a =-= a' → f a =-= f a'
  ap-seq [] = []
  ap-seq (p ◃∙ s) = ap f p ◃∙ ap-seq s

  private
    ap-seq-∙-= : {a a' : A} → (s : a =-= a')
      → ap f (↯ s) == ↯ (ap-seq s)
    ap-seq-∙-= [] = idp
    ap-seq-∙-= (p ◃∙ []) = idp
    ap-seq-∙-= (p ◃∙ s@(_ ◃∙ _)) =
      ap-∙ f p (↯ s) ∙
      ap (λ u → ap f p ∙ u) (ap-seq-∙-= s)

  ap-seq-∙ : {a a' : A} (s : a =-= a')
    → (ap f (↯ s) ◃∎) =ₛ ap-seq s
  ap-seq-∙ s = =ₛ-in (ap-seq-∙-= s)

  ∙-ap-seq : {a a' : A} (s : a =-= a')
    → ap-seq s =ₛ (ap f (↯ s) ◃∎)
  ∙-ap-seq s = !ₛ (ap-seq-∙ s)

  ap-seq-=ₛ : {a a' : A} {s t : a =-= a'}
    → s =ₛ t
    → ap-seq s =ₛ ap-seq t
  ap-seq-=ₛ {s = s} {t = t} (=ₛ-in p) =
    ap-seq s
      =ₛ⟨ ∙-ap-seq s ⟩
    ap f (↯ s) ◃∎
      =ₛ₁⟨ ap (ap f) p ⟩
    ap f (↯ t) ◃∎
      =ₛ⟨ ap-seq-∙ t ⟩
    ap-seq t ∎ₛ

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap2-seq : {a a' : A} {b b' : B} → a =-= a' → b =-= b' → f a b =-= f a' b'
  ap2-seq [] [] = []
  ap2-seq {a = a} [] t@(_ ◃∙ _) = ap-seq (f a) t
  ap2-seq {b = b} s@(_ ◃∙ _) [] = ap-seq (λ a → f a b) s
  ap2-seq (p ◃∙ s) (q ◃∙ t) = ap2 f p q ◃∙ ap2-seq s t

  private
    ap2-seq-∙-= : {a a' : A} {b b' : B}
      (s : a =-= a') (t : b =-= b')
      → ap2 f (↯ s) (↯ t) == ↯ (ap2-seq s t)
    ap2-seq-∙-= [] [] = idp
    ap2-seq-∙-= {a = a} [] t@(_ ◃∙ _) =
      ap2 f idp (↯ t)
        =⟨ ap2-idp-l f (↯ t) ⟩
      ap (f a) (↯ t)
        =⟨ =ₛ-out (ap-seq-∙ (f a) t) ⟩
      ↯ (ap-seq (f a) t) =∎
    ap2-seq-∙-= {b = b} s@(_ ◃∙ _) [] =
      ap2 f (↯ s) idp
        =⟨ ap2-idp-r f (↯ s) ⟩
      ap (λ a → f a b) (↯ s)
        =⟨ =ₛ-out (ap-seq-∙ (λ a → f a b) s ) ⟩
      ↯ (ap-seq (λ a → f a b) s) =∎
    ap2-seq-∙-= (p ◃∙ []) (q ◃∙ []) = idp
    ap2-seq-∙-= {a' = a'} (p ◃∙ []) (q ◃∙ t@(_ ◃∙ _)) =
      ap2 f p (q ∙ ↯ t)
        =⟨ ap (λ r → ap2 f r (q ∙ ↯ t)) (! (∙-unit-r p)) ⟩
      ap2 f (p ∙ idp) (q ∙ ↯ t)
        =⟨ ap2-∙ f p idp q (↯ t) ⟩
      ap2 f p q ∙ ap2 f idp (↯ t)
        =⟨ ap (ap2 f p q ∙_) (ap2-idp-l f (↯ t)) ⟩
      ap2 f p q ∙ ap (f a') (↯ t)
        =⟨ ap (ap2 f p q ∙_) (=ₛ-out (ap-seq-∙ (f a') t)) ⟩
      ap2 f p q ∙ ↯ (ap-seq (f a') t) =∎
    ap2-seq-∙-= {b' = b'} (p ◃∙ s@(_ ◃∙ _)) (q ◃∙ []) =
      ap2 f (p ∙ ↯ s) q
        =⟨ ap (ap2 f (p ∙ ↯ s)) (! (∙-unit-r q)) ⟩
      ap2 f (p ∙ ↯ s) (q ∙ idp)
        =⟨ ap2-∙ f p (↯ s) q idp ⟩
      ap2 f p q ∙ ap2 f (↯ s) idp
        =⟨ ap (ap2 f p q ∙_) (ap2-idp-r f (↯ s)) ⟩
      ap2 f p q ∙ ap (λ a → f a b') (↯ s)
        =⟨ ap (ap2 f p q ∙_) (=ₛ-out (ap-seq-∙ (λ a → f a b') s)) ⟩
      ap2 f p q ∙ ↯ (ap-seq (λ a → f a b') s) =∎
    ap2-seq-∙-= (p ◃∙ s@(_ ◃∙ _)) (q ◃∙ t@(_ ◃∙ _)) =
      ap2 f (p ∙ ↯ s) (q ∙ ↯ t)
        =⟨ ap2-∙ f p (↯ s) q (↯ t) ⟩
      ap2 f p q ∙ ap2 f (↯ s) (↯ t)
        =⟨ ap (ap2 f p q ∙_) (ap2-seq-∙-= s t) ⟩
      ap2 f p q ∙ ↯ (ap2-seq s t) =∎

  ap2-seq-∙ : {a a' : A} {b b' : B}
    (s : a =-= a') (t : b =-= b')
    → ap2 f (↯ s) (↯ t) ◃∎ =ₛ ap2-seq s t
  ap2-seq-∙ s t = =ₛ-in (ap2-seq-∙-= s t)

  ∙-ap2-seq : {a a' : A} {b b' : B}
    (s : a =-= a') (t : b =-= b')
    → ap2-seq s t =ₛ ap2 f (↯ s) (↯ t) ◃∎
  ∙-ap2-seq s t = !ₛ (ap2-seq-∙ s t)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where

  module _ {a a' a'' : A} (p : a == a') (p' : a' == a'') where
    ap-∘-∙-coh-seq₁ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₁ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∙ (g ∘ f) p p' ⟫
      ap (g ∘ f) p ∙ ap (g ∘ f) p'
        =⟪ ap2 _∙_ (ap-∘ g f p) (ap-∘ g f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

    ap-∘-∙-coh-seq₂ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₂ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∘ g f (p ∙ p') ⟫
      ap g (ap f (p ∙ p'))
        =⟪ ap (ap g) (ap-∙ f p p') ⟫
      ap g (ap f p ∙ ap f p')
        =⟪ ap-∙ g (ap f p) (ap f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

  ap-∘-∙-coh :  {a a' a'' : A} (p : a == a') (p' : a' == a'')
    → ap-∘-∙-coh-seq₁ p p' =ₛ ap-∘-∙-coh-seq₂ p p'
  ap-∘-∙-coh idp idp = =ₛ-in idp

ap-comm-cst : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C)
  {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
  (c : C) (h : ∀ b → f a₀ b == c)
  → ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q =-=
    ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
ap-comm-cst f {a₀} {a₁} p {b₀} {b₁} q c h =
  ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q
    =⟪ ap (ap (λ a → f a b₀) p ∙_) $ =ₛ-out $
       homotopy-naturality' (λ b → f a₁ b) (λ _ → c) h' q ⟫
  ap (λ a → f a b₀) p ∙ h' b₀ ∙ ap (λ _ → c) q ∙ ! (h' b₁)
    =⟪ ap (ap (λ a → f a b₀) p ∙_) $
       ap (_$ h) (transp-naturality {B = λ a → ∀ b → f a b == c} (λ hh → hh b₀ ∙ ap (λ _ → c) q ∙ ! (hh b₁)) p) ⟫
  ap (λ a → f a b₀) p ∙ transport (λ a → f a b₀ == f a b₁) p k₀
    =⟪ ! (ap-transport f p k₀) ⟫
  k₀ ∙ ap (λ a → f a b₁) p
    =⟪ ap (_∙ ap (λ a → f a b₁) p) $ ! $ =ₛ-out $
       homotopy-naturality' (λ b → f a₀ b) (λ _ → c) h q ⟫
  ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p ∎∎
  where
    h' : ∀ b → f a₁ b == c
    h' = transport (λ a → ∀ b → f a b == c) p h
    k₀ : f a₀ b₀ == f a₀ b₁
    k₀ = h b₀ ∙ ap (λ _ → c) q ∙ ! (h b₁)

ap-comm-cst-coh : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C)
  {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
  (c : C) (h : ∀ b → f a₀ b == c)
  → ap-comm f p q ◃∎ =ₛ
    ap-comm-cst f p q c h
ap-comm-cst-coh f {a₀} p@idp {b₀} q@idp c h = !ₛ $
  ap (idp ∙_) (! (!-inv-r (h b₀))) ◃∙
  idp ◃∙
  ! (∙-unit-r (h b₀ ∙ ! (h b₀))) ◃∙
  ap (_∙ idp) (! (! (!-inv-r (h b₀)))) ◃∎
    =ₛ⟨ 1 & 1 & expand [] ⟩
  ap (idp ∙_) (! (!-inv-r (h b₀))) ◃∙
  ! (∙-unit-r (h b₀ ∙ ! (h b₀))) ◃∙
  ap (_∙ idp) (! (! (!-inv-r (h b₀)))) ◃∎
    =ₛ₁⟨ 0 & 1 & ap-idf (! (!-inv-r (h b₀))) ⟩
  ! (!-inv-r (h b₀)) ◃∙
  ! (∙-unit-r (h b₀ ∙ ! (h b₀))) ◃∙
  ap (_∙ idp) (! (! (!-inv-r (h b₀)))) ◃∎
    =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality-from-idf (_∙ idp) (λ p → ! (∙-unit-r p)) (! (! (!-inv-r (h b₀))))) ⟩
  ! (!-inv-r (h b₀)) ◃∙
  ! (! (!-inv-r (h b₀))) ◃∙
  idp ◃∎
    =ₛ₁⟨ 0 & 2 & !-inv-r (! (!-inv-r (h b₀))) ⟩
  idp ◃∙ idp ◃∎
    =ₛ⟨ 0 & 1 & expand [] ⟩
  idp ◃∎ ∎ₛ

apd= : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
       (p : f ∼ g) {a b : A} (q : a == b)
       → apd f q ▹ p b == p a ◃ apd g q
apd= {B = B} p {b} idp = idp▹ {B = B} (p b) ∙ ! (◃idp {B = B} (p b))

apd=-red : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
           (p : f ∼ g) {a b : A} (q : a == b)
           {u : B b} (s : g b =-= u)
           → apd f q ▹ ↯ (p b ◃∙ s) == p a ◃ (apd g q ▹ ↯ s)
apd=-red {B = B} p {b} idp s = coh (p b) s  where

  coh : ∀ {i} {A : Type i} {u v w : A} (p : u == v) (s : v =-= w)
    → idp ∙' ↯ (p ◃∙ s) == p ∙ idp ∙' ↯ s
  coh idp [] = idp
  coh idp (p ◃∙ s) = idp
