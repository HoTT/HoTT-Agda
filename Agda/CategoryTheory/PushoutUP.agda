{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.PushoutUP {m : Level}
  (A B C : Set m) (f : C → A) (g : C → B)
  (P : Set m → Set m) ⦃ PA : P A ⦄ ⦃ PB : P B ⦄ ⦃ PC : P C ⦄ where

-- Idea : [Cone E = (A → E) ×_(C → E) (B → E)]
record cone (tp : Set m) : Set (suc m) where
  constructor _,_,_
  field
    A→tp : A → tp
    B→tp : B → tp
    h : (c : C) → (A→tp (f c)) ≡ (B→tp (g c))

cone-eq : (tp : Set m) {a1 a2 : A → tp} {b1 b2 : B → tp}
  {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)} 
  (p1 : a1 ≡ a2) (p2 : b1 ≡ b2) (p3 : transport _ p1 (transport _ p2 h1) ≡ h2)
  → (a1 , b1 , h1) ≡ (a2 , b2 , h2)
cone-eq tp (refl _) (refl _) (refl _) = refl _

postulate
  cone-eq-new : (tp : Set m) {a1 a2 : A → tp} {b1 b2 : B → tp}
  {h1 : (c : C) → a1 (f c) ≡ b1 (g c)} {h2 : (c : C) → a2 (f c) ≡ b2 (g c)} 
  (p1 : a1 ≡ a2) (p2 : b1 ≡ b2)
  (p3 : (c : C) → happly p1 (f c) ∘ h2 c ≡ h1 c ∘ happly p2 (g c))
  → (a1 , b1 , h1) ≡ (a2 , b2 , h2)

-- (c : C) → happly p1 (f c) ∘ h2 c ≡ h1 c ∘ happly p2 (g c)

open import CategoryTheory.PullbackDef

cone-to-pullback : (tp : Set m) → cone tp
  → pullback (A → tp) (B → tp) (C → tp) (λ u → u ◯ f) (λ u → u ◯ g)
cone-to-pullback tp (a , b , h) = (a , b , funext-dep h)

pullback-to-cone : (tp : Set m)
  → pullback (A → tp) (B → tp) (C → tp) (λ u → u ◯ f) (λ u → u ◯ g)
  → cone tp
pullback-to-cone tp (a , b , h) = (a , b , happly h)

cone-equiv-pullback : (tp : Set m)
  → cone tp ≃ pullback (A → tp) (B → tp) (C → tp) (λ u → u ◯ f) (λ u → u ◯ g)
cone-equiv-pullback tp = (cone-to-pullback tp
  , iso-is-eq _
    (pullback-to-cone tp)
    (λ p → map (λ u → _ , _ , u) (funext-dep-happly _))
    (λ c → map (λ u → _ , _ , u) (happly-funext-dep _)))

pullback-equiv-cone : (tp : Set m)
  → pullback (A → tp) (B → tp) (C → tp) (λ u → u ◯ f) (λ u → u ◯ g) ≃ cone tp
pullback-equiv-cone tp = (pullback-to-cone tp
  , iso-is-eq _
    (cone-to-pullback tp)
    (λ c → map (λ u → _ , _ , u) (happly-funext-dep _))
    (λ p → map (λ u → _ , _ , u) (funext-dep-happly _)))

compose-cone-map : (D E : Set m) (Dcone : cone D) → ((f : D → E) → cone E)
compose-cone-map D E (A→tp , B→tp , h) f =
  ((f ◯ A→tp) , (f ◯ B→tp) , (λ c → map f (h c)))

is-pushout : (D : Set m) ⦃ PD : P D ⦄ (Dcone : cone D) → Set _
is-pushout D Dcone = (E : Set m) ⦃ PE : P E ⦄
                     → is-equiv (compose-cone-map D E Dcone)

compose-cone-map-compose : (D E F : Set m) (Dcone : cone D) (f : D → E)
  (g : E → F)
  → compose-cone-map E F (compose-cone-map D E Dcone f) g
    ≡ compose-cone-map D F Dcone (g ◯ f)
compose-cone-map-compose D E F Dcone f g =
  map (λ u → ((g ◯ (f ◯ cone.A→tp Dcone)) , (g ◯ (f ◯ cone.B→tp Dcone)) , u))
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
