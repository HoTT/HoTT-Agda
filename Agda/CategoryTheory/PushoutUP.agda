{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.PushoutUP {m : Level}
  (A B C : Set m) (f : C → A) (g : C → B)
  (P : Set m → Set m) ⦃ PA : P A ⦄ ⦃ PB : P B ⦄ ⦃ PC : P C ⦄ where

-- Idea : [Cone E = (A → E) ×_(C → E) (B → E)]
record cone (top : Set m) : Set (suc m) where
  constructor _,_,_
  field
    A→top : A → top
    B→top : B → top
    h : (c : C) → (A→top (f c)) ≡ (B→top (g c))

open import CategoryTheory.PullbackDef

cone-equiv-pullback : (top : Set m) → cone top ≃ pullback (A → top) (B → top) (C → top) (λ u → u ◯ f) (λ u → u ◯ g)
cone-equiv-pullback top = ((λ c → (cone.A→top c , cone.B→top c , funext-dep (cone.h c)))
  , iso-is-eq _
    (λ p → pullback.a _ _ _ _ _ p , pullback.b _ _ _ _ _ p , happly (pullback.h _ _ _ _ _ p))
    (λ p → map (λ u → _ , _ , u) (funext-dep-happly _))
    (λ c → map (λ u → _ , _ , u) (happly-funext-dep _)))

compose-cone-map : (D E : Set m) (Dcone : cone D) → ((f : D → E) → cone E)
compose-cone-map D E (A→top , B→top , h) f = ((f ◯ A→top) , (f ◯ B→top) , (λ c → map f (h c)))

is-pushout : (D : Set m) ⦃ PD : P D ⦄ (Dcone : cone D) → Set _
is-pushout D Dcone = (E : Set m) ⦃ PE : P E ⦄ → is-equiv (compose-cone-map D E Dcone)

compose-cone-map-compose : (D E F : Set m) (Dcone : cone D) (f : D → E) (g : E → F)
  → compose-cone-map E F (compose-cone-map D E Dcone f) g ≡ compose-cone-map D F Dcone (g ◯ f)
compose-cone-map-compose D E F Dcone f g = map (λ u → ((g ◯ (f ◯ cone.A→top Dcone)) , (g ◯ (f ◯ cone.B→top Dcone)) , u))
                                           (funext-dep (λ c → compose-map g f (cone.h Dcone c)))

module UniquenessPushout (D : Set m) ⦃ PD : P D ⦄ (Dcone : cone D) (Dpushout : is-pushout D Dcone)
  (E : Set m) ⦃ PE : P E ⦄ (Econe : cone E) (Epushout : is-pushout E Econe) where

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

  D→E→D : (λ x → E→D (D→E x)) ≡ (λ x → x)
  D→E→D = equiv-is-inj (compose-cone-map D D Dcone , Dpushout D) _ _
    (! (compose-cone-map-compose D E D Dcone D→E E→D)
    ∘ (map (λ u → compose-cone-map E D u E→D) (inverse-right-inverse DE-eq Econe)
    ∘ (inverse-right-inverse ED-eq Dcone ∘ map (λ u → _ , _ , u) (funext-dep (λ c → ! (map-idmap _))))))

  E→D→E : (λ x → D→E (E→D x)) ≡ (λ x → x)
  E→D→E = equiv-is-inj (compose-cone-map E E Econe , Epushout E) _ _
    (! (compose-cone-map-compose E D E Econe E→D D→E)
    ∘ (map (λ u → compose-cone-map D E u D→E) (inverse-right-inverse ED-eq Dcone)
    ∘ (inverse-right-inverse DE-eq Econe ∘ map (λ u → _ , _ , u) (funext-dep (λ c → ! (map-idmap _))))))

  D≃E : D ≃ E
  D≃E = (D→E , iso-is-eq _ E→D (happly E→D→E) (happly D→E→D))
