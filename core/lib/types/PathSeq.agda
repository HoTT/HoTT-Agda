{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Paths

module lib.types.PathSeq where

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

infix  15 _∎∎
infixr 10 _=⟪_⟫_
infixr 10 _=⟪idp⟫_

data PathSeq {i} {A : Type i} : A → A → Type i where
  _∎∎ : (a : A) → PathSeq a a
  _=⟪_⟫_ : (a : A) {a' a'' : A} (p : a == a') (s : PathSeq a' a'') → PathSeq a a''

infix 30 _=-=_
_=-=_ = PathSeq

_=⟪idp⟫_ : ∀ {i} {A : Type i} (a : A) {a' : A} (s : PathSeq a a') → PathSeq a a'
a =⟪idp⟫ s = s

module _ {i} {A : Type i} where

  infix 0 ↯_

  ↯_ : {a a' : A} (s : PathSeq a a') → a == a'
  ↯ a ∎∎ = idp
  ↯ a =⟪ p ⟫ a' ∎∎ = p
  ↯ a =⟪ p ⟫ s = p ∙ (↯ s)

  {- concatenation -}
  infixr 80 _∙∙_
  _∙∙_ : {a a' a'' : A}
    → PathSeq a a' → PathSeq a' a'' → PathSeq a a''
  _∙∙_ (a ∎∎) t = t
  _∙∙_ (a =⟪ p ⟫ a') t = a =⟪ p ⟫ (a' ∙∙ t)

  ∙∙-assoc : {a a' a'' a''' : A}
    (s : a =-= a') (t : a' =-= a'') (u : a'' =-= a''')
    → (s ∙∙ t) ∙∙ u == s ∙∙ (t ∙∙ u)
  ∙∙-assoc (a ∎∎) t u = idp
  ∙∙-assoc (a =⟪ p ⟫ s) t u = ap (a =⟪ p ⟫_) (∙∙-assoc s t u)

  ∙∙-unit-r : {a a' : A} (s : a =-= a')
    → s ∙∙ (a' ∎∎) == s
  ∙∙-unit-r (a ∎∎) = idp
  ∙∙-unit-r (a =⟪ p ⟫ s) = ap (a =⟪ p ⟫_) (∙∙-unit-r s)

  infixr 80 _◃∙_
  _◃∙_ : {a a' a'' : A}
    → a == a' → PathSeq a' a'' → PathSeq a a''
  _◃∙_ {a} p s = a =⟪ p ⟫ s

  infixl 80 _∙▹_
  _∙▹_ : {a a' a'' : A}
    → PathSeq a a' → a' == a'' → PathSeq a a''
  _∙▹_ {a} {a'} {a''} s p = s ∙∙ (a' =⟪ p ⟫ a'' ∎∎)

  infix 90 _◃∎
  _◃∎ : {a a' : A} → a == a' → PathSeq a a'
  _◃∎ {a} {a'} p = a =⟪ p ⟫ a' ∎∎

  seq-! : {a a' : A} → a =-= a' → a' =-= a
  seq-! (a ∎∎) = a ∎∎
  seq-! (a =⟪ p ⟫ s) = seq-! s ∙▹ ! p

  ↯-∙∙ : {a a' a'' : A} (s : PathSeq a a') (t : PathSeq a' a'')
    → (↯ (s ∙∙ t)) == (↯ s) ∙ (↯ t)
  ↯-∙∙ (a ∎∎) t = idp
  ↯-∙∙ (a =⟪ p ⟫ a' ∎∎) (.a' ∎∎) = ! (∙-unit-r p)
  ↯-∙∙ (a =⟪ p ⟫ a' ∎∎) (.a' =⟪ p' ⟫ t) = idp
  ↯-∙∙ (a =⟪ p ⟫ a' =⟪ p' ⟫ s) t =
    ap (λ y → p ∙ y) (↯-∙∙ (a' =⟪ p' ⟫ s) t) ∙
    ! (∙-assoc p (↯ (a' =⟪ p' ⟫ s)) (↯ t))

  infix 30 _=↯=_
  _=↯=_ : {a a' : A} → PathSeq a a' → PathSeq a a' → Type i
  _=↯=_ s t = (↯ s) == (↯ t)

  abstract
    post-rearrange'-in : {a a' a'' : A}
      → (r : a =-= a'') (q : a' == a'') (p : a =-= a')
      → r =↯= (p ∙▹ q)
      → (r ∙▹ (! q)) =↯= p
    post-rearrange'-in r idp p e =
      (↯ (r ∙▹ idp))
        =⟨ ↯-∙∙ r (idp ◃∎) ⟩
      (↯ r) ∙ idp
        =⟨ ∙-unit-r (↯ r) ⟩
      (↯ r)
        =⟨ e ⟩
      (↯ (p ∙▹ idp))
        =⟨ ↯-∙∙ p (idp ◃∎) ⟩
      (↯ p) ∙ idp
        =⟨ ∙-unit-r (↯ p) ⟩
      (↯ p) =∎

    post-rearrange-in : {a a' a'' : A}
      → (p : a =-= a') (r : a =-= a'') (q : a' == a'')
      → p ∙▹ q =↯= r
      → p =↯= r ∙▹ (! q)
    post-rearrange-in p r q e = ! (post-rearrange'-in r q p (! e))

    post-rearrange'-in-seq : {a a' a'' : A}
      → (r : a =-= a'') (q : a' =-= a'') (p : a =-= a')
      → r =↯= p ∙∙ q
      → r ∙∙ (seq-! q) =↯= p
    post-rearrange'-in-seq r (a ∎∎) p e = ap ↯_ (∙∙-unit-r r) ∙ e ∙ ap ↯_ (∙∙-unit-r p)
    post-rearrange'-in-seq r (a =⟪ q ⟫ s) p e =
      (↯ r ∙∙ (seq-! s ∙▹ ! q))
        =⟨ ap ↯_ (! (∙∙-assoc r (seq-! s) (! q ◃∎))) ⟩
      (↯ (r ∙∙ seq-! s) ∙▹ ! q)
        =⟨ post-rearrange'-in (r ∙∙ seq-! s) q p
             (post-rearrange'-in-seq r s (p ∙▹ q) (e ∙ ap ↯_ (! (∙∙-assoc p (q ◃∎) s)))) ⟩
      (↯ p) =∎

    post-rearrange-in-seq : {a a' a'' : A}
      → (p : a =-= a') (r : a =-= a'') (q : a' =-= a'')
      → (p ∙∙ q) =↯= r
      → p =↯= (r ∙∙ (seq-! q))
    post-rearrange-in-seq p r q e = ! (post-rearrange'-in-seq r q p (! e))

    pre-rotate-in-seq : {a a' a'' : A}
      → (q : a' =-= a'') (p : a =-= a') (r : a =-= a'')
      → p ∙∙ q =↯= r
      → q =↯= seq-! p ∙∙ r
    pre-rotate-in-seq q (a ∎∎) r e = e
    pre-rotate-in-seq q (a =⟪ p ⟫ s) r e =
      (↯ q)
        =⟨ pre-rotate-in-seq q s (! p ◃∙ r)
             (pre-rotate-in (↯ s ∙∙ q) p (↯ r) (! (↯-∙∙ (p ◃∎) (s ∙∙ q)) ∙ e) ∙
              ! (↯-∙∙ (! p ◃∎) r)) ⟩
      (↯ seq-! s ∙∙ ! p ◃∙ r)
        =⟨ ap ↯_ (! (∙∙-assoc (seq-! s) (! p ◃∎) r)) ⟩
      (↯ seq-! (p ◃∙ s) ∙∙ r) =∎

    pre-rotate-in'-seq : {a a' a'' : A}
      → (p : a =-= a') (r : a =-= a'') (q : a' =-= a'')
      → r =↯= p ∙∙ q
      → seq-! p ∙∙ r =↯= q
    pre-rotate-in'-seq p r q e = ! (pre-rotate-in-seq q p r (! e))

  point-from-start : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
  point-from-start O {a} s = a
  point-from-start (S n) (a ∎∎) = a
  point-from-start (S n) (a =⟪ p ⟫ s) = point-from-start n s

  _-! : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-start n s) a'
  (O -!) s = s
  (S n -!) (a ∎∎) = a ∎∎
  (S n -!) (a =⟪ p ⟫ s) = (n -!) s

  private
    last1 : {a a' : A} (s : PathSeq a a') → A
    last1 (a ∎∎) = a
    last1 (a =⟪ p ⟫ a' ∎∎) = a
    last1 (a =⟪ p ⟫ s) = last1 s

    strip : {a a' : A} (s : PathSeq a a') → PathSeq a (last1 s)
    strip (a ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' =⟪ p' ⟫ s) = a =⟪ p ⟫ strip (a' =⟪ p' ⟫ s)

    point-from-end : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end O {a} {a'} s = a'
    point-from-end (S n) s = point-from-end n (strip s)

  !- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-end n s)
  !- O s = s
  !- (S n) s = !- n (strip s)

  _-# : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-start n s)
  (O -#) s = _ ∎∎
  (S n -#) (a ∎∎) = a ∎∎
  (S n -#) (a =⟪ p ⟫ s) = a =⟪ p ⟫ (n -#) s

  abstract
    ∙∙-#-! : {a a' : A} (s : PathSeq a a') (n : ℕ)
      → s == (n -#) s ∙∙ (n -!) s
    ∙∙-#-! s O = idp
    ∙∙-#-! (a ∎∎) (S n) = idp
    ∙∙-#-! (a =⟪ p ⟫ s) (S n) = ap (λ v → p ◃∙ v) (∙∙-#-! s n)

    ↯-#-! : {a a' : A} (s : PathSeq a a') (n : ℕ)
      → (↯ s) == (↯ (n -#) s) ∙ (↯ (n -!) s)
    ↯-#-! s n =
      (↯ s)
        =⟨ ap ↯_ (∙∙-#-! s n) ⟩
      (↯ (n -#) s ∙∙ (n -!) s)
        =⟨ ↯-∙∙ ((n -#) s) ((n -!) s) ⟩
      (↯ (n -#) s) ∙ (↯ (n -!) s) =∎

  private
    split : {a a' : A} (s : PathSeq a a')
      → Σ A (λ a'' → (PathSeq a a'') × (a'' == a'))
    split (a ∎∎) = (a , ((a ∎∎) , idp))
    split (a =⟪ p ⟫ a' ∎∎) = (a , ((a ∎∎) , p))
    split (a =⟪ p ⟫ s) = let (a'' , (t , q)) = split s in (a'' , ((a =⟪ p ⟫ t) , q))

    point-from-end' : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end' n (a ∎∎) = a
    point-from-end' O (a =⟪ p ⟫ s) = point-from-end' O s
    point-from-end' (S n) (a =⟪ p ⟫ s) = point-from-end' n (fst (snd (split (a =⟪ p ⟫ s))))

  #- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-end' n s) a'
  #- n (a ∎∎) = a ∎∎
  #- O (a =⟪ p ⟫ s) = #- O s
  #- (S n) (a =⟪ p ⟫ s) = let (a' , (t , q)) = split (a =⟪ p ⟫ s) in #- n t ∙▹ q

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

  -- 'ₛ' is for sequence
  data _=ₛ_ (s t : a =-= a') : Type i where
    =ₛ-in : s =↯= t → s =ₛ t

  =ₛ-out : {s t : a =-= a'} → s =ₛ t → s =↯= t
  =ₛ-out (=ₛ-in p) = p

  =-=ₛ-equiv : (s t : a =-= a') → (s =↯= t) ≃ (s =ₛ t)
  =-=ₛ-equiv s t = equiv =ₛ-in =ₛ-out (λ {(=ₛ-in p) → idp}) (λ p → idp)

  =ₛ-level : {s t : a =-= a'} {n : ℕ₋₂}
    → has-level (S (S n)) A → has-level n (s =ₛ t)
  =ₛ-level {s} {t} {n} A-level =
    transport (has-level n) (ua (=-=ₛ-equiv s t)) $
    has-level-apply (has-level-apply A-level _ _) _ _

  !ₛ : {s t : a =-= a'} → s =ₛ t → t =ₛ s
  !ₛ (=ₛ-in p) = =ₛ-in (! p)

  _∙ₛ_ : {s t u : a =-= a'} → s =ₛ t → t =ₛ u → s =ₛ u
  _∙ₛ_ (=ₛ-in p) (=ₛ-in q) = =ₛ-in (p ∙ q)

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
      → (path : (↯ (n -#) ((m -!) s)) ∙' _=ₛ-free-start_.start-matches tail-matches ==
                _=ₛ-free-end_.end-matches init-matches ∙ (↯ (o -#) ((m -!) t)))
      → t =ₛ u
      → s =ₛ u
    _=ₛ⟨_&_&_&_⟩_ s {t} {u} m n o {{init-matches}} {{tail-matches}} path q =
      =ₛ-in $
        (↯ s)
          =⟨ ↯-#-! s m ⟩
        (↯ (m -#) s) ∙ (↯ (m -!) s)
          =⟨ ap ((↯ (m -#) s) ∙_) (↯-#-! ((m -!) s) n) ⟩
        (↯ (m -#) s) ∙ (↯ (n -#) ((m -!) s)) ∙ (↯ (n -!) ((m -!) s))
          =⟨ ap (λ w → (↯ (m -#) s) ∙ (↯ (n -#) ((m -!) s)) ∙ w) tail-matches.path ⟩
        (↯ (m -#) s) ∙ (↯ (n -#) ((m -!) s)) ∙ tail-matches.start-matches ∙ (↯ (o -!) ((m -!) t))
          =⟨ ap (λ w → (↯ (m -#) s) ∙ w) (! (∙-assoc (↯ (n -#) ((m -!) s)) tail-matches.start-matches (↯ (o -!) ((m -!) t)))) ⟩
        (↯ (m -#) s) ∙ ((↯ (n -#) ((m -!) s)) ∙ tail-matches.start-matches) ∙ (↯ (o -!) ((m -!) t))
          =⟨ ap (λ w → (↯ (m -#) s) ∙ w ∙ (↯ (o -!) ((m -!) t)))
                (∙=∙' (↯ (n -#) ((m -!) s)) tail-matches.start-matches ∙ path) ⟩
        (↯ (m -#) s) ∙ (init-matches.end-matches ∙ (↯ (o -#) ((m -!) t))) ∙ (↯ (o -!) ((m -!) t))
          =⟨ ap (λ w → (↯ (m -#) s) ∙ w) (∙-assoc init-matches.end-matches (↯ (o -#) ((m -!) t)) (↯ (o -!) ((m -!) t))) ⟩
        (↯ (m -#) s) ∙ init-matches.end-matches ∙ (↯ (o -#) ((m -!) t)) ∙ (↯ (o -!) ((m -!) t))
          =⟨ ! (∙-assoc (↯ (m -#) s) init-matches.end-matches ((↯ (o -#) ((m -!) t)) ∙ (↯ (o -!) ((m -!) t)))) ⟩
        ((↯ (m -#) s) ∙ init-matches.end-matches) ∙ (↯ (o -#) ((m -!) t)) ∙ (↯ (o -!) ((m -!) t))
          =⟨ ap (λ w → w ∙ (↯ (o -#) ((m -!) t)) ∙ (↯ (o -!) ((m -!) t)))
                (∙=∙' (↯ (m -#) s) init-matches.end-matches ∙ init-matches.path) ⟩
        (↯ (m -#) t) ∙ (↯ (o -#) ((m -!) t)) ∙ (↯ (o -!) ((m -!) t))
          =⟨ ! (ap ((↯ (m -#) t) ∙_) (↯-#-! ((m -!) t) o)) ⟩
        (↯ (m -#) t) ∙ (↯ (m -!) t)
          =⟨ ! (↯-#-! t m) ⟩
        (↯ t)
          =⟨ =ₛ-out q ⟩
        (↯ u) =∎
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
        → (↯ ((n -#) s) ∙∙ t ∙∙ ((m -!) ((n -!) s))) == q
        → (↯ s) == q
      _=↯=⟨_&_&_&_⟩_ {a} {a'} {q} s n m t p p' =
        (↯ s)
          =⟨ ↯-#-! s n ⟩
        (↯ (n -#) s) ∙ (↯ (n -!) s)
          =⟨ ap ((↯ (n -#) s) ∙_) (↯-#-! ((n -!) s) m) ⟩
        (↯ (n -#) s) ∙ (↯ (m -#) ((n -!) s)) ∙ (↯ (m -!) ((n -!) s))
          =⟨ ap (λ v → (↯ (n -#) s) ∙ v ∙ (↯ (m -!) ((n -!) s))) p ⟩
        (↯ (n -#) s) ∙ (↯ t) ∙ (↯ (m -!) ((n -!) s))
          =⟨ ap (λ v → (↯ (n -#) s) ∙ v) (! (↯-∙∙ t ((m -!) ((n -!) s)))) ⟩
        (↯ (n -#) s) ∙ (↯ t ∙∙ (m -!) ((n -!) s))
          =⟨ ! (↯-∙∙ ((n -#) s) (t ∙∙ (m -!) ((n -!) s))) ⟩
        (↯ (n -#) s ∙∙ t ∙∙ (m -!) ((n -!) s))
          =⟨ p' ⟩
        q =∎

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
      → (↯ (n -#) ((m -!) s)) == r
      → (m -#) s ∙∙ r ◃∙ (n -!) ((m -!) s) =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_&_&_⟩_ s m n {r} p p' = s =ₛ⟨ m & n & =ₛ-in {t = r ◃∎} p ⟩ p'

    infixr 10 _=ₛ₁⟨_⟩_
    _=ₛ₁⟨_⟩_ : {a a' : A} (s : a =-= a') {u : a =-= a'}
      → {r : a == a'}
      → (↯ s) == r
      → r ◃∎ =ₛ u
      → s =ₛ u
    _=ₛ₁⟨_⟩_ s {r} p p' = =ₛ-in p ∙ₛ p'

module _ {i} {A : Type i} where

  pre-rotate-in-=ₛ : {a a' a'' : A} {q : a' =-= a''} {p : a =-= a'} {r : a =-= a''}
    → p ∙∙ q =ₛ r
    → q =ₛ seq-! p ∙∙ r
  pre-rotate-in-=ₛ {q = q} {p = p} {r = r} e =
    =ₛ-in (pre-rotate-in-seq q p r (=ₛ-out e))

  pre-rotate'-in-=ₛ : {a a' a'' : A} {p : a =-= a'} {r : a =-= a''} {q : a' =-= a''}
    → r =ₛ p ∙∙ q
    → seq-! p ∙∙ r =ₛ q
  pre-rotate'-in-=ₛ {p = p} {r = r} {q = q} e =
    =ₛ-in (pre-rotate-in'-seq p r q (=ₛ-out e))

  post-rearrange'-in-=ₛ : {a a' a'' : A}
    → {r : a =-= a''} {q : a' =-= a''} {p : a =-= a'}
    → r =ₛ p ∙∙ q
    → r ∙∙ (seq-! q) =ₛ p
  post-rearrange'-in-=ₛ {r = r} {q = q} {p = p} e =
    =ₛ-in (post-rearrange'-in-seq r q p (=ₛ-out e))

  post-rearrange-in-=ₛ : {a a' a'' : A}
    → {p : a =-= a'} {r : a =-= a''} {q : a' =-= a''}
    → p ∙∙ q =ₛ r
    → p =ₛ r ∙∙ (seq-! q)
  post-rearrange-in-=ₛ {p = p} {r = r} {q = q} e =
    =ₛ-in (post-rearrange-in-seq p r q (=ₛ-out e))

  homotopy-naturality-=ₛ : ∀ {k} {B : Type k} (f g : A → B)
    (h : (x : A) → f x == g x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality-=ₛ f g h p =
   =ₛ-in (homotopy-naturality f g h p)

  homotopy-naturality-to-idf-=ₛ : (f : A → A)
    (h : (x : A) → f x == x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ p ◃∎
  homotopy-naturality-to-idf-=ₛ f h p =
    =ₛ-in (homotopy-naturality-to-idf f h p)

  homotopy-naturality-from-idf-=ₛ : (g : A → A)
    (h : (x : A) → x == g x) {x y : A} (p : x == y)
    → p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality-from-idf-=ₛ g h p =
    =ₛ-in (homotopy-naturality-from-idf g h p)

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-seq : {a a' : A} → a =-= a' → f a =-= f a'
  ap-seq (a ∎∎) = f a ∎∎
  ap-seq (a =⟪ p ⟫ s) = f a =⟪ ap f p ⟫ ap-seq s

  private
    ap-seq-∙-= : {a a' : A} → (s : a =-= a')
      → ap f (↯ s) == (↯ ap-seq s)
    ap-seq-∙-= (a ∎∎) = idp
    ap-seq-∙-= (a =⟪ p ⟫ a' ∎∎) = idp
    ap-seq-∙-= (a =⟪ p ⟫ a' =⟪ p' ⟫ s) =
      ap-∙ f p (↯ a' =⟪ p' ⟫ s) ∙
      ap (λ s → ap f p ∙ s) (ap-seq-∙-= (a' =⟪ p' ⟫ s))

  ap-seq-∙ : {a a' : A} → (s : a =-= a')
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

apd= : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
       (p : f ∼ g) {a b : A} (q : a == b)
       → apd f q ▹ p b == p a ◃ apd g q
apd= {B = B} p {b} idp = idp▹ {B = B} (p b) ∙ ! (◃idp {B = B} (p b))

apd=-red : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
           (p : f ∼ g) {a b : A} (q : a == b)
           {u : B b} (s : g b =-= u)
           → apd f q ▹ (↯ _ =⟪ p b ⟫ s) == p a ◃ (apd g q ▹ (↯ s))
apd=-red {B = B} p {b} idp s = coh (p b) s  where

  coh : ∀ {i} {A : Type i} {u v w : A} (p : u == v) (s : v =-= w)
    → (idp ∙' (↯ _ =⟪ p ⟫ s)) == p ∙ idp ∙' (↯ s)
  coh idp (a ∎∎) = idp
  coh idp (a =⟪ p₁ ⟫ s₁) = idp
