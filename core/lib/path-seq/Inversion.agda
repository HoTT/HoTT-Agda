{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.path-seq.Concat
open import lib.path-seq.Reasoning

module lib.path-seq.Inversion {i} {A : Type i} where

seq-! : {a a' : A} → a =-= a' → a' =-= a
seq-! [] = []
seq-! (p ◃∙ s) = seq-! s ∙▹ ! p

seq-!-∙▹ : {a a' a'' : A} (s : a =-= a') (q : a' == a'')
  → seq-! (s ∙▹ q) == ! q ◃∙ seq-! s
seq-!-∙▹ [] q = idp
seq-!-∙▹ (p ◃∙ s) q = ap (_∙▹ ! p) (seq-!-∙▹ s q)

seq-!-seq-! : {a a' : A} (s : a =-= a')
  → seq-! (seq-! s) == s
seq-!-seq-! [] = idp
seq-!-seq-! (p ◃∙ s) =
  seq-! (seq-! s ∙▹ ! p)
    =⟨ seq-!-∙▹ (seq-! s) (! p) ⟩
  ! (! p) ◃∙ seq-! (seq-! s)
    =⟨ ap2 _◃∙_ (!-! p) (seq-!-seq-! s) ⟩
  p ◃∙ s =∎

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
