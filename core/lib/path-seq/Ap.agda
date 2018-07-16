{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.path-seq.Reasoning

module lib.path-seq.Ap where

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
