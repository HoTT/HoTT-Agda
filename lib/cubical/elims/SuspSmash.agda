{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.CubeMove
open import lib.cubical.elims.CofWedge

module lib.cubical.elims.SuspSmash where

module _ {i j k} {X : Ptd i} {Y : Ptd j} {C : Type k}
  (f : Suspension (Smash X Y) → C) (g : Suspension (Smash X Y) → C)
  (north* : f (north _) == g (north _))
  (south* : f (south _) == g (south _))
  (cod* : (s : fst X × fst Y) → Square north* (ap f (merid _ (cfcod _ s)))
                                (ap g (merid _ (cfcod _ s))) south*)
  where

  private
    base* = transport
      (λ κ → Square north* (ap f (merid _ κ)) (ap g (merid _ κ)) south*)
      (! (cfglue _ (winl (snd X))))
      (cod* (snd X , snd Y))

    CubeType : (w : Wedge X Y)
      → Square north* (ap f (merid _ (cfcod _ (∨-in-× X Y w))))
               (ap g (merid _ (cfcod _ (∨-in-× X Y w)))) south*
      → Type _
    CubeType w sq =
      Cube base* sq
        (natural-square (λ _ → north*) (cfglue _ w))
        (natural-square (ap f ∘ merid _) (cfglue _ w))
        (natural-square (ap g ∘ merid _) (cfglue _ w))
        (natural-square (λ _ → south*) (cfglue _ w))

    fill : (w : Wedge X Y)
      (sq : Square north* (ap f (merid _ (cfcod _ (∨-in-× X Y w))))
                   (ap g (merid _ (cfcod _ (∨-in-× X Y w)))) south*)
      → Σ (Square north* idp idp north*) (λ p → CubeType w (p ⊡h sq))
    fill w sq =
      (fst fill' ,
       cube-right-from-front (fst fill') sq (snd fill'))
      where
      fill' = fill-cube-right _ _ _ _ _

    fill0 = fill (winl (snd X)) (cod* (snd X , snd Y))
    fillX = λ x → fill (winl x) (fst fill0 ⊡h cod* (x , snd Y))
    fillY = λ y → fill (winr y) (fst fill0 ⊡h cod* (snd X , y))

    fillX0 : fst (fillX (snd X)) == hid-square
    fillX0 = ⊡h-unit-l-unique _ (fst fill0 ⊡h cod* (snd X , snd Y))
               (fill-cube-right-unique (snd (fillX (snd X)))
                ∙ ! (fill-cube-right-unique (snd fill0)))

    fillY0 : fst (fillY (snd Y)) == hid-square
    fillY0 = ⊡h-unit-l-unique _ (fst fill0 ⊡h cod* (snd X , snd Y))
               (fill-cube-right-unique (snd (fillY (snd Y)))
                ∙ ! (fill-cube-right-unique
                       (snd (fill (winr (snd Y)) (cod* (snd X , snd Y)))))
                ∙ ! (ap (λ w → fst (fill w (cod* (∨-in-× X Y w)))
                                ⊡h cod* (snd X , snd Y))
                     wglue))
      where
      fill-square : (w : Wedge X Y)
        → Square north* (ap f (merid _ (cfcod _ (∨-in-× X Y w))))
                 (ap g (merid _ (cfcod _ (∨-in-× X Y w)))) south*
      fill-square w =
        fst (fill-cube-right base*
              (natural-square (λ _ → north*) (cfglue _ w))
              (natural-square (ap f ∘ merid _) (cfglue _ w))
              (natural-square (ap g ∘ merid _) (cfglue _ w))
              (natural-square (λ _ → south*) (cfglue _ w)))

    abstract
      coh : (s : Smash X Y)
        → north* == south* [ (λ z → f z == g z) ↓ merid _ s ]
      coh = ↓-='-from-square ∘ cof-wedge-square-elim _ _ _ _
        base*
        (λ {(x , y) →
          fst (fillX x) ⊡h fst (fillY y) ⊡h fst fill0 ⊡h cod* (x , y)})
        (λ x → transport (λ sq → CubeType (winl x) (fst (fillX x) ⊡h sq))
          (! (ap (λ sq' → sq' ⊡h fst fill0 ⊡h cod* (x , snd Y)) fillY0
              ∙ ⊡h-unit-l (fst fill0 ⊡h cod* (x , snd Y))))
          (snd (fillX x)))
        (λ y → transport (CubeType (winr y))
          (! (ap (λ sq' → sq' ⊡h fst (fillY y) ⊡h fst fill0 ⊡h cod* (snd X , y))
                 fillX0
              ∙ ⊡h-unit-l (fst (fillY y) ⊡h fst fill0 ⊡h cod* (snd X , y))))
        (snd (fillY y)))

  susp-smash-path-elim : ((σ : Suspension (Smash X Y)) → f σ == g σ)
  susp-smash-path-elim = Suspension-elim _ north* south* coh
