{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Function
open import lib.PathFunctor
open import lib.PathGroupoid

module lib.path-seq.Concat {i} {A : Type i} where

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
  → s ∙∙ [] == s
∙∙-unit-r [] = idp
∙∙-unit-r (p ◃∙ s) = ap (p ◃∙_) (∙∙-unit-r s)

infixl 80 _∙▹_
_∙▹_ : {a a' a'' : A}
  → a =-= a' → a' == a'' → a =-= a''
_∙▹_ {a} {a'} {a''} s p = s ∙∙ (p ◃∙ [])

↯-∙∙ : {a a' a'' : A} (s : a =-= a') (t : a' =-= a'')
  → ↯ (s ∙∙ t) == ↯ s ∙ ↯ t
↯-∙∙ [] t = idp
↯-∙∙ (p ◃∙ []) [] = ! (∙-unit-r p)
↯-∙∙ (p ◃∙ []) (p' ◃∙ t) = idp
↯-∙∙ (p ◃∙ s@(_ ◃∙ _)) t =
  ap (λ y → p ∙ y) (↯-∙∙ s t) ∙
  ! (∙-assoc p (↯ s) (↯ t))
