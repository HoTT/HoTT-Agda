{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PullbackDef

-- We only consider the universal property internally to a fixed
-- universe [Set i]. If we don’t, we would have to consider an universe
-- polymorphic [P] and I don’t want to quantify over universe polymorphic things
module Homotopy.PullbackUP {i} (d : pullback-diag i)
  (P : Set i → Set i) ⦃ PA : P (pullback-diag.A d) ⦄
  ⦃ PB : P (pullback-diag.B d) ⦄ ⦃ PC : P (pullback-diag.C d) ⦄ where

open pullback-diag d

record cone (top : Set i) : Set i where
  constructor _,_,_
  field
    top→A : top → A
    top→B : top → B
    h : (t : top) → f (top→A t) ≡ g (top→B t)

top→D : (top : Set i) → pullback-diag i
top→D top = diag (top → A), (top → B), (top → C), (λ h → f ◯ h), (λ h → g ◯ h)

pullback-to-cone : (top : Set i) → (pullback (top→D top) → cone top)
pullback-to-cone top (top→A , top→B , h) = (top→A , top→B , happly h)

cone-to-pullback : (top : Set i) → (cone top → pullback (top→D top))
cone-to-pullback top (a , b , h) = (a , b , funext h)

pullback-to-cone-equiv : (top : Set i) → is-equiv (pullback-to-cone top)
pullback-to-cone-equiv top = iso-is-eq _ (cone-to-pullback top)
  (λ y → ap (λ u → _ , _ , u) (happly-funext _))
  (λ x → ap (λ u → _ , _ , u) (funext-happly _))

cone-to-pullback-equiv : (top : Set i) → is-equiv (cone-to-pullback top)
cone-to-pullback-equiv top = iso-is-eq _ (pullback-to-cone top)
  (λ x → ap (λ u → _ , _ , u) (funext-happly _))
  (λ y → ap (λ u → _ , _ , u) (happly-funext _))

compose-cone-map : (D E : Set i) (Dcone : cone D)
  → ((f : E → D) → cone E)
compose-cone-map D E (top→A , top→B , h) f =
  ((top→A ◯ f) , (top→B ◯ f) , λ x → h (f x))

is-pullback : (D : Set i) ⦃ PD : P D ⦄ (Dcone : cone D) → Set _
is-pullback D Dcone = (E : Set i) ⦃ PE : P E ⦄
                        → is-equiv (compose-cone-map D E Dcone)
