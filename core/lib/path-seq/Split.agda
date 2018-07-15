{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Function
open import lib.PathFunctor
open import lib.PathGroupoid

open import lib.path-seq.Concat

module lib.path-seq.Split {i} {A : Type i} where

point-from-start : (n : ℕ) {a a' : A} (s : a =-= a') → A
point-from-start O {a} s = a
point-from-start (S n) {a = a} [] = a
point-from-start (S n) (p ◃∙ s) = point-from-start n s

drop : (n : ℕ) {a a' : A} (s : a =-= a') → point-from-start n s =-= a'
drop 0 s = s
drop (S n) [] = []
drop (S n) (p ◃∙ s) = drop n s

tail : {a a' : A} (s : a =-= a') → point-from-start 1 s =-= a'
tail = drop 1

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

take : (n : ℕ) {a a' : A} (s : a =-= a') → a =-= point-from-start n s
take O s = []
take (S n) [] = []
take (S n) (p ◃∙ s) = p ◃∙ take n s

private
  take-drop-split' : {a a' : A} (n : ℕ) (s : a =-= a')
    → s == take n s ∙∙ drop n s
  take-drop-split' O s = idp
  take-drop-split' (S n) [] = idp
  take-drop-split' (S n) (p ◃∙ s) = ap (λ v → p ◃∙ v) (take-drop-split' n s)

abstract
  take-drop-split : {a a' : A} (n : ℕ) (s : a =-= a')
    → ↯ s ◃∎ =ₛ ↯ (take n s) ◃∙ ↯ (drop n s) ◃∎
  take-drop-split n s = =ₛ-in $
    ↯ s
      =⟨ ap ↯ (take-drop-split' n s) ⟩
    ↯ (take n s ∙∙ drop n s)
      =⟨ ↯-∙∙ (take n s) (drop n s) ⟩
    ↯ (take n s) ∙ ↯ (drop n s) =∎

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

0! = drop 0
1! = drop 1
2! = drop 2
3! = drop 3
4! = drop 4
5! = drop 5

infix 120 _#0 _#1 _#2 _#3 _#4 _#5
_#0 = #- 0
_#1 = #- 1
_#2 = #- 2
_#3 = #- 3
_#4 = #- 4
_#5 = #- 5

0# = take 0
1# = take 1
2# = take 2
3# = take 3
4# = take 4
5# = take 5
