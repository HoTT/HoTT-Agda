{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PushoutDef

module Homotopy.PushoutUP {m : Level} (D : pushout-diag m)
  (P : Set m → Set m) ⦃ PA : P (pushout-diag.A D) ⦄
  ⦃ PB : P (pushout-diag.B D) ⦄ ⦃ PC : P (pushout-diag.C D) ⦄ where

open pushout-diag D

-- Idea : [Cone E = (A → E) ×_(C → E) (B → E)]
record cone (top : Set m) : Set m where
  constructor _,_,_
  field
    A→top : A → top
    B→top : B → top
    h : (c : C) → (A→top (f c)) ≡ (B→top (g c))
open cone public

cone-eq : (top : Set m) {a1 a2 : A → top} {b1 b2 : B → top}
  {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)} 
  (p1 : a1 ≡ a2) (p2 : b1 ≡ b2) (p3 : transport _ p1 (transport _ p2 h1) ≡ h2)
  → (a1 , b1 , h1) ≡ (a2 , b2 , h2)
cone-eq top (refl _) (refl _) (refl _) = refl _

postulate
  cone-eq-new : (top : Set m) {a1 a2 : A → top} {b1 b2 : B → top}
    {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)} 
    (p1 : a1 ≡ a2) (p2 : b1 ≡ b2)
    (p3 : (c : C) → happly p1 (f c) ∘ h2 c ≡ h1 c ∘ happly p2 (g c))
    → (a1 , b1 , h1) ≡ (a2 , b2 , h2)

-- (c : C) → happly p1 (f c) ∘ h2 c ≡ h1 c ∘ happly p2 (g c)

open import Homotopy.PullbackDef

D→top : (top : Set m) → pullback-diag m
D→top top = diag (A → top) , (B → top) , (C → top) , (λ u → u ◯ f) , (λ u → u ◯ g)

cone-to-pullback : (top : Set m) → cone top → pullback (D→top top)
cone-to-pullback top (a , b , h) = (a , b , funext-dep h)

pullback-to-cone : (top : Set m)
  → pullback (D→top top)
  → cone top
pullback-to-cone top (a , b , h) = (a , b , happly h)

cone-equiv-pullback : (top : Set m) → cone top ≃ pullback (D→top top)
cone-equiv-pullback top = (cone-to-pullback top
  , iso-is-eq _
    (pullback-to-cone top)
    (λ p → map (λ u → _ , _ , u) (funext-dep-happly _))
    (λ c → map (λ u → _ , _ , u) (happly-funext-dep _)))

pullback-equiv-cone : (top : Set m) → pullback (D→top top) ≃ cone top
pullback-equiv-cone top = (pullback-to-cone top
  , iso-is-eq _
    (cone-to-pullback top)
    (λ c → map (λ u → _ , _ , u) (happly-funext-dep _))
    (λ p → map (λ u → _ , _ , u) (funext-dep-happly _)))

compose-cone-map : (D E : Set m) (Dcone : cone D) → ((f : D → E) → cone E)
compose-cone-map D E (A→top , B→top , h) f =
  ((f ◯ A→top) , (f ◯ B→top) , (λ c → map f (h c)))

is-pushout : (D : Set m) ⦃ PD : P D ⦄ (Dcone : cone D) → Set _
is-pushout D Dcone = (E : Set m) ⦃ PE : P E ⦄
                     → is-equiv (compose-cone-map D E Dcone)

compose-cone-map-compose : (D E F : Set m) (Dcone : cone D) (f : D → E)
  (g : E → F)
  → compose-cone-map E F (compose-cone-map D E Dcone f) g
    ≡ compose-cone-map D F Dcone (g ◯ f)
compose-cone-map-compose D E F Dcone f g =
  map (λ u → ((g ◯ (f ◯ cone.A→top Dcone)) , (g ◯ (f ◯ cone.B→top Dcone)) , u))
      (funext-dep (λ c → compose-map g f (cone.h Dcone c)))

module UniquenessPushout (D : Set m) ⦃ PD : P D ⦄ (Dcone : cone D)
  (Dpushout : is-pushout D Dcone) (E : Set m) ⦃ PE : P E ⦄ (Econe : cone E)
  (Epushout : is-pushout E Econe) where

  DE-eq : (D → E) ≃ cone E
  DE-eq = (compose-cone-map D E Dcone , Dpushout E)

  ED-eq : (E → D) ≃ cone D
  ED-eq = (compose-cone-map E D Econe , Epushout D)

  DD-eq : (D → D) ≃ cone D
  DD-eq = (compose-cone-map D D Dcone , Dpushout D)

  EE-eq : (E → E) ≃ cone E
  EE-eq = (compose-cone-map E E Econe , Epushout E)

  D→E : D → E
  D→E = (DE-eq ⁻¹) $ Econe

  E→D : E → D
  E→D = (ED-eq ⁻¹) $ Dcone

  abstract
    D→E→D : (λ x → E→D (D→E x)) ≡ (λ x → x)
    D→E→D = equiv-is-inj (compose-cone-map D D Dcone , Dpushout D) _ _
      (! (compose-cone-map-compose D E D Dcone D→E E→D)
      ∘ (map (λ u → compose-cone-map E D u E→D)
             (inverse-right-inverse DE-eq Econe)
      ∘ (inverse-right-inverse ED-eq Dcone
        ∘ map (λ u → _ , _ , u) (funext-dep (λ c → ! (map-idmap _))))))

    E→D→E : (λ x → D→E (E→D x)) ≡ (λ x → x)
    E→D→E = equiv-is-inj (compose-cone-map E E Econe , Epushout E) _ _
      (! (compose-cone-map-compose E D E Econe E→D D→E)
      ∘ (map (λ u → compose-cone-map D E u D→E)
             (inverse-right-inverse ED-eq Dcone)
      ∘ (inverse-right-inverse DE-eq Econe
        ∘ map (λ u → _ , _ , u) (funext-dep (λ c → ! (map-idmap _))))))

    D≃E : D ≃ E
    D≃E = (D→E , iso-is-eq _ E→D (happly E→D→E) (happly D→E→D))
