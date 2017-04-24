{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.PushoutProduct {i j k l}
  {A : Type i} {B : Type j}
  {A' : Type k} {B' : Type l}
  where

□-span : (f : A → B) (g : A' → B') → Span
□-span f g = span (B × A') (A × B') (A × A')
  (λ { (a , a') → f a , a'})
  (λ { (a , a') → a , g a' })

module PshoutProd (f : A → B) (g : A' → B') =
  PushoutRec {d = □-span f g}
    (λ { (b , a') → b , g a' })
    (λ { (a , b') → f a , b' })
    (λ { (a , a') → idp })

_□_ : (f : A → B) (g : A' → B') → Pushout (□-span f g) → B × B'
f □ g = PshoutProd.f f g

□-glue-β : (f : A → B) (g : A' → B') (a : A) (a' : A') → ap (f □ g) (glue (a , a')) == idp
□-glue-β f g = {!PshoutProd.glue-β!}
-- Agda bug is keeping me from finishing this ...
  
module _ (f : A → B) (g : A' → B') where

  private
    abstract
    
      ↓-□=cst-out : ∀ {a a' b b'} {p p' : (f a , g a') == (b , b')}
        → p == p' [ (λ w → (f □ g) w == (b , b')) ↓ glue (a , a') ]
        → p == p'
      ↓-□=cst-out {p' = idp} q = ↓-app=cst-out' q ∙ □-glue-β f g _ _

      ↓-□=cst-in : ∀ {a a' b b'} {p p' : (f a , g a') == (b , b')}
        → p == p'
        → p == p' [ (λ w → (f □ g) w == (b , b')) ↓ glue (a , a') ]
      ↓-□=cst-in {p' = idp} q = ↓-app=cst-in' (q ∙ ! (□-glue-β f g _ _))


      ↓-□=cst-β : ∀ {a a' b b'} {p p' : (f a , g a') == (b , b')}
        (q : p == p')
        → ↓-□=cst-out (↓-□=cst-in q) == q
      ↓-□=cst-β {a} {a'} {p' = idp} idp = {!!}  ∙ !-inv-l (□-glue-β f g a a')


  □-hfiber-to : (b : B) (b' : B')
    → hfiber (f □ g) (b , b') → hfiber f b * hfiber g b'
  □-hfiber-to b b' = uncurry $ Pushout-elim
    (λ { (_ , a') → λ p → right (a' , snd×= p) })
    (λ { (a , _) → λ p → left (a , fst×= p) }) {!!}

  --
  -- Here is the main theorem
  --
  
  □-hfiber : (b : B) (b' : B')
    → hfiber (f □ g) (b , b') ≃ hfiber f b * hfiber g b'
  □-hfiber b b' = {!!}
