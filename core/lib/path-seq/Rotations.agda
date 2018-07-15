{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

open import lib.path-seq.Concat
open import lib.path-seq.Inversion
open import lib.path-seq.Reasoning

module lib.path-seq.Rotations {i} {A : Type i} where

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

pre-rotate-out : {a a' a'' : A} {p : a == a'} {q : a' =-= a''} {r : a =-= a''}
  → q =ₛ ! p ◃∙ r
  → p ◃∙ q =ₛ r
pre-rotate-out {p = idp} {q = q} {r = r} e =
  idp ◃∙ q
    =ₛ⟨ =ₛ-in (↯-∙∙ (idp ◃∎) q) ⟩
  q
    =ₛ⟨ e ⟩
  idp ◃∙ r
    =ₛ⟨ =ₛ-in (↯-∙∙ (idp ◃∎) r) ⟩
  r ∎ₛ

pre-rotate'-in : {a a' a'' : A} {p : a == a'} {r : a =-= a''} {q : a' =-= a''}
  → r =ₛ p ◃∙ q
  → ! p ◃∙ r =ₛ q
pre-rotate'-in e =
  !ₛ (pre-rotate-in (!ₛ e))

pre-rotate'-out : {a a' a'' : A} {r : a =-= a''} {p : a == a'} {q : a' =-= a''}
  → ! p ◃∙ r =ₛ q
  → r =ₛ p ◃∙ q
pre-rotate'-out e =
  !ₛ (pre-rotate-out (!ₛ e))

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

post-rotate-out : {a a' a'' : A}
  → {p : a =-= a'} {q : a' == a''} {r : a =-= a''}
  → p =ₛ r ∙▹ ! q
  → p ∙▹ q =ₛ r
post-rotate-out {p = p} {q = q} {r = r} e = =ₛ-in $
  ↯ (p ∙▹ q)
    =⟨ ap (λ v → ↯ (p ∙▹ v)) (! (!-! q)) ⟩
  ↯ (p ∙▹ ! (! q))
    =⟨ =ₛ-out (post-rotate'-in {r = p} {q = ! q} {p = r} e) ⟩
  ↯ r =∎

post-rotate'-seq-in : {a a' a'' : A}
  → {r : a =-= a''} {q : a' =-= a''} {p : a =-= a'}
  → r =ₛ p ∙∙ q
  → r ∙∙ seq-! q =ₛ p
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

post-rotate'-seq-out : {a a' a'' : A}
  → {r : a =-= a''} {p : a =-= a'} {q : a' =-= a''}
  → r ∙∙ seq-! q =ₛ p
  → r =ₛ p ∙∙ q
post-rotate'-seq-out {r = r} {p = p} {q = q} e =
  r
    =ₛ⟨ post-rotate-seq-in {p = r} {r = p} {q = seq-! q} e ⟩
  p ∙∙ seq-! (seq-! q)
    =ₛ⟨ =ₛ-in (ap (λ v → ↯ (p ∙∙ v)) (seq-!-seq-! q)) ⟩
  p ∙∙ q ∎ₛ

post-rotate-seq-out : {a a' a'' : A}
  → {p : a =-= a'} {q : a' =-= a''} {r : a =-= a''}
  → p =ₛ r ∙∙ seq-! q
  → p ∙∙ q =ₛ r
post-rotate-seq-out e =
  !ₛ (post-rotate'-seq-out (!ₛ e))
