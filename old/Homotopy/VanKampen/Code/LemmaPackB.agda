{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pushout
open import Homotopy.VanKampen.Guide

module Homotopy.VanKampen.Code.LemmaPackB {i} (d : pushout-diag i)
  (l : legend i (pushout-diag.C d)) where

  open pushout-diag d
  open legend l

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation
  open import Homotopy.VanKampen.SplitCode d l

  abstract
    trans-q-code-a : ∀ {a₁ a₂} (q : a₁ ≡ a₂) {a₃} (p : _ ≡₀ a₃)
      → transport (λ x → code-a x a₃) q (a a₁ p)
      ≡ a a₂ (proj (! q) ∘₀ p)
    trans-q-code-a refl p = ap (λ x → a _ x) $ ! $ refl₀-left-unit p

    trans-!q-code-a : ∀ {a₁ a₂} (q : a₂ ≡ a₁) {a₃} (p : _ ≡₀ a₃)
      → transport (λ x → code-a x a₃) (! q) (a a₁ p)
      ≡ a a₂ (proj q ∘₀ p)
    trans-!q-code-a refl p = ap (λ x → a _ x) $ ! $ refl₀-left-unit p

    trans-q-code-ba : ∀ {a₁ a₂} (q : a₁ ≡ a₂) {a₃} n co (p : _ ≡₀ a₃)
      → transport (λ x → code-a x a₃) q (ba a₁ n co p)
      ≡ ba a₂ n (transport (λ x → code-b x (g $ loc n)) q co) p
    trans-q-code-ba refl n co p = refl

    trans-q-code-ab : ∀ {a₁ a₂} (q : a₁ ≡ a₂) {b₃} n co (p : _ ≡₀ b₃)
      → transport (λ x → code-b x b₃) q (ab a₁ n co p)
      ≡ ab a₂ n (transport (λ x → code-a x (f $ loc n)) q co) p
    trans-q-code-ab refl n co p = refl
