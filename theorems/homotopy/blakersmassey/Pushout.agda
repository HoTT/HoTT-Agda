{-# OPTIONS --without-K --rewriting #-}

open import HoTT

-- custom pushout for Blakers-Massey 

module homotopy.blakersmassey.Pushout {i j k}
  {A : Type i} {B : Type j} (Q : A → B → Type k) where

  bmspan : Span {i} {j} {lmax i (lmax j k)}
  bmspan = span A B (Σ A λ a → Σ B λ b → Q a b) fst (fst ∘ snd)

  BMPushout : Type (lmax i (lmax j k))
  BMPushout = Pushout bmspan

  bmleft : A → BMPushout
  bmleft = left

  bmright : B → BMPushout
  bmright = right

  bmglue : ∀ {a b} → Q a b → bmleft a == bmright b
  bmglue {a} {b} q = glue (a , b , q)

  module BMPushoutElim {l} {P : BMPushout → Type l}
    (bmleft* : (a : A) → P (bmleft a)) (bmright* : (b : B) → P (bmright b))
    (bmglue* : ∀ {a b} (q : Q a b) → bmleft* a == bmright* b [ P ↓ bmglue q ]) where

    private
      module P = PushoutElim {d = bmspan} {P = P}
        bmleft* bmright* (λ c → bmglue* (snd (snd c)))

    f = P.f

    glue-β : ∀ {a b} (q : Q a b) → apd f (bmglue q) == bmglue* q
    glue-β q = P.glue-β (_ , _ , q)

  BMPushout-elim = BMPushoutElim.f

  module BMPushoutRec {l} {D : Type l}
    (bmleft* : A → D) (bmright* : B → D)
    (bmglue* : ∀ {a b} (q : Q a b) → bmleft* a == bmright* b) where

    private
      module P = PushoutRec {d = bmspan} {D = D}
        bmleft* bmright* (λ c → bmglue* (snd (snd c)))

    f = P.f

    glue-β : ∀ {a b} (q : Q a b) → ap f (bmglue q) == bmglue* q
    glue-β q = P.glue-β (_ , _ , q)
