{-# OPTIONS --without-K #-}

open import Base
open import CategoryTheory.PullbackDef

-- We only consider the universal property internally to a fixed
-- universe [Set i]. If we don’t, we would have to consider an universe
-- polymorphic [P] and I don’t want to quantify over universe polymorphic things
module CategoryTheory.PullbackUP {i}
  (A B C : Set i) (f : A → C) (g : B → C)
  (P : Set i → Set i) ⦃ PA : P A ⦄ ⦃ PB : P B ⦄ ⦃ PC : P C ⦄ where

record cocone (top : Set i) : Set i where
  constructor _,_,_
  field
    top→A : top → A
    top→B : top → B
    h : (t : top) → f (top→A t) ≡ g (top→B t)

top→D : (top : Set i) → pullback-diag i
top→D top = diag (top → A), (top → B), (top → C), (λ h → f ◯ h), (λ h → g ◯ h)

pullback-to-cocone : (top : Set i) → (pullback (top→D top) → cocone top)
pullback-to-cocone top (top→A , top→B , h) = (top→A , top→B , happly h)

cocone-to-pullback : (top : Set i) → (cocone top → pullback (top→D top))
cocone-to-pullback top (a , b , h) = (a , b , funext-dep h)

pullback-to-cocone-equiv : (top : Set i) → is-equiv (pullback-to-cocone top)
pullback-to-cocone-equiv top = iso-is-eq _ (cocone-to-pullback top)
  (λ y → map (λ u → _ , _ , u) (happly-funext-dep _))
  (λ x → map (λ u → _ , _ , u) (funext-dep-happly _))

cocone-to-pullback-equiv : (top : Set i) → is-equiv (cocone-to-pullback top)
cocone-to-pullback-equiv top = iso-is-eq _ (pullback-to-cocone top)
  (λ x → map (λ u → _ , _ , u) (funext-dep-happly _))
  (λ y → map (λ u → _ , _ , u) (happly-funext-dep _))

compose-cocone-map : (D E : Set i) (Dcocone : cocone D)
  → ((f : E → D) → cocone E)
compose-cocone-map D E (top→A , top→B , h) f =
  ((top→A ◯ f) , (top→B ◯ f) , λ x → h (f x))

is-pullback : (D : Set i) ⦃ PD : P D ⦄ (Dcocone : cocone D) → Set _
is-pullback D Dcocone = (E : Set i) ⦃ PE : P E ⦄
                        → is-equiv (compose-cocone-map D E Dcocone)
