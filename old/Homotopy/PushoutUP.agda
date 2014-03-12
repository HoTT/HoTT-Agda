{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PushoutDef

module Homotopy.PushoutUP {m} (D : pushout-diag m) (P : Set m → Set m)
  ⦃ PA : P (pushout-diag.A D) ⦄ ⦃ PB : P (pushout-diag.B D) ⦄
  ⦃ PC : P (pushout-diag.C D) ⦄ where

open pushout-diag D

-- Idea : [cocone E = (A → E) ×_(C → E) (B → E)]
record cocone (top : Set m) : Set m where
  constructor _,_,_
  field
    A→top : A → top
    B→top : B → top
    h : (c : C) → (A→top (f c)) ≡ (B→top (g c))
open cocone public

cocone-eq-raw : (top : Set m) {a1 a2 : A → top} {b1 b2 : B → top}
  {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)}
  (p1 : a1 ≡ a2) (p2 : b1 ≡ b2) (p3 : transport _ p1 (transport _ p2 h1) ≡ h2)
  → (a1 , b1 , h1) ≡ (a2 , b2 , h2)
cocone-eq-raw top refl refl refl = refl

cocone-eq : (top : Set m) {a1 a2 : A → top} {b1 b2 : B → top}
  {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)}
  (p1 : a1 ≡ a2) (p2 : b1 ≡ b2)
  (p3 : (c : C) → happly p1 (f c) ∘ h2 c ≡ h1 c ∘ happly p2 (g c))
  → (a1 , b1 , h1) ≡ (a2 , b2 , h2)
cocone-eq top refl refl p3 =
  cocone-eq-raw top refl refl
    (funext (λ c → ! (refl-right-unit _) ∘ ! (p3 c)))

open import Homotopy.PullbackDef

D→top : (top : Set m) → pullback-diag m
D→top top = diag (A → top) , (B → top) , (C → top)
                 , (λ u → u ◯ f) , (λ u → u ◯ g)

cocone-to-pullback : (top : Set m) → cocone top → pullback (D→top top)
cocone-to-pullback top (a , b , h) = (a , b , funext h)

pullback-to-cocone : (top : Set m)
  → pullback (D→top top)
  → cocone top
pullback-to-cocone top (a , b , h) = (a , b , happly h)

cocone-equiv-pullback : (top : Set m) → cocone top ≃ pullback (D→top top)
cocone-equiv-pullback top = (cocone-to-pullback top
  , iso-is-eq _
    (pullback-to-cocone top)
    (λ p → ap (λ u → _ , _ , u) (funext-happly _))
    (λ c → ap (λ u → _ , _ , u) (happly-funext _)))

pullback-equiv-cocone : (top : Set m) → pullback (D→top top) ≃ cocone top
pullback-equiv-cocone top = (pullback-to-cocone top
  , iso-is-eq _
    (cocone-to-pullback top)
    (λ c → ap (λ u → _ , _ , u) (happly-funext _))
    (λ p → ap (λ u → _ , _ , u) (funext-happly _)))

compose-cocone-map : (D E : Set m) (Dcocone : cocone D)
  → ((f : D → E) → cocone E)
compose-cocone-map D E (A→top , B→top , h) f =
  ((f ◯ A→top) , (f ◯ B→top) , (λ c → ap f (h c)))

is-pushout : (D : Set m) ⦃ PD : P D ⦄ (Dcocone : cocone D) → Set _
is-pushout D Dcocone = (E : Set m) ⦃ PE : P E ⦄
                     → is-equiv (compose-cocone-map D E Dcocone)

compose-cocone-map-compose : (D E F : Set m) (Dcocone : cocone D) (f : D → E)
  (g : E → F)
  → compose-cocone-map E F (compose-cocone-map D E Dcocone f) g
    ≡ compose-cocone-map D F Dcocone (g ◯ f)
compose-cocone-map-compose D E F Dcocone f g =
  ap (λ u → ((g ◯ (f ◯ cocone.A→top Dcocone))
             , (g ◯ (f ◯ cocone.B→top Dcocone)) , u))
      (funext (λ c → compose-ap g f (cocone.h Dcocone c)))

module _ (D : Set m) ⦃ PD : P D ⦄ (Dcocone : cocone D)
  (Dpushout : is-pushout D Dcocone) (E : Set m) ⦃ PE : P E ⦄
  (Ecocone : cocone E) (Epushout : is-pushout E Ecocone) where

  private
    DE-eq : (D → E) ≃ cocone E
    DE-eq = (compose-cocone-map D E Dcocone , Dpushout E)

    ED-eq : (E → D) ≃ cocone D
    ED-eq = (compose-cocone-map E D Ecocone , Epushout D)

    DD-eq : (D → D) ≃ cocone D
    DD-eq = (compose-cocone-map D D Dcocone , Dpushout D)

    EE-eq : (E → E) ≃ cocone E
    EE-eq = (compose-cocone-map E E Ecocone , Epushout E)

    D→E : D → E
    D→E = (DE-eq ⁻¹) ☆ Ecocone

    E→D : E → D
    E→D = (ED-eq ⁻¹) ☆ Dcocone

    abstract
      D→E→D : (λ x → E→D (D→E x)) ≡ (λ x → x)
      D→E→D = equiv-is-inj (compose-cocone-map D D Dcocone , Dpushout D) _ _
        (! (compose-cocone-map-compose D E D Dcocone D→E E→D)
        ∘ (ap (λ u → compose-cocone-map E D u E→D)
               (inverse-right-inverse DE-eq Ecocone)
        ∘ (inverse-right-inverse ED-eq Dcocone
          ∘ ap (λ u → _ , _ , u) (funext (λ c → ! (ap-id _))))))

      E→D→E : (λ x → D→E (E→D x)) ≡ (λ x → x)
      E→D→E = equiv-is-inj (compose-cocone-map E E Ecocone , Epushout E) _ _
        (! (compose-cocone-map-compose E D E Ecocone E→D D→E)
        ∘ (ap (λ u → compose-cocone-map D E u D→E)
               (inverse-right-inverse ED-eq Dcocone)
        ∘ (inverse-right-inverse DE-eq Ecocone
          ∘ ap (λ u → _ , _ , u) (funext (λ c → ! (ap-id _))))))

  pushout-equiv-pushout : D ≃ E
  pushout-equiv-pushout = (D→E , iso-is-eq _ E→D (happly E→D→E) (happly D→E→D))
