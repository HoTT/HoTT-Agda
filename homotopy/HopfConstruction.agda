{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace

module homotopy.HopfConstruction {i} (A : Type i) {-(c : is-connected 0 A)-}
  (hA : HSpaceStructure A) where

μ : A → A → A
μ = HSpaceStructure.μ hA

postulate
  μ-is-equiv : (a : A) → is-equiv (μ a)
  μ2-is-equiv : (a : A) → is-equiv (λ a' → μ a' a)

μ-equiv : A → A ≃ A
μ-equiv a = (μ a , μ-is-equiv a)

μ-equiv2 : A → A ≃ A
μ-equiv2 a = ((λ a' → μ a' a) , μ2-is-equiv a)

module H = SuspensionRecType A A A μ-equiv

s : Span
s = span (⊤ × A) (⊤ × A) (A × A)
         (λ cc' → (tt , snd cc')) (λ cc' → (tt , uncurry μ cc'))

lemma : Σ (Suspension A) H.f == Pushout s
lemma = H.flattening

join-span-flipped : Span
join-span-flipped = span A A (A × A) snd fst

eq : (A × A) ≃ (A × A)
eq = equiv to from to-from from-to  where

  to : A × A → A × A
  to (a , a') = (μ a a' , a')

  from : A × A → A × A
  from (a , a') = (<– (μ-equiv2 a') a , a')

  to-from : (a : A × A) → to (from a) == a
  to-from (a , a') = pair×= (<–-inv-r (μ-equiv2 a') a) idp

  from-to : (a : A × A) → from (to a) == a
  from-to (a , a') = pair×= (<–-inv-l (μ-equiv2 a') a) idp

x : s == join-span-flipped
x = span= (equiv snd (_,_ tt) (λ b → idp) (λ a → idp))
          (equiv snd (_,_ tt) (λ b → idp) (λ a → idp))
          eq (λ a → idp) (λ a → idp)

record FibSeq {i j k ℓ} (A : Type i) (B : Type j) (C : Type k) (c : C)
  : Type (lmax (lmax i j) (lmax k (lsucc ℓ))) where
  constructor fibSeq
  field
    fibration : C → Type ℓ
    fiber : fibration c ≃ A
    total : Σ C fibration ≃ B
