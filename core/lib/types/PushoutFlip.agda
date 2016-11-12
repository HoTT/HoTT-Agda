{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Span

module lib.types.PushoutFlip where

module _ {i j k} {d : Span {i} {j} {k}} where

  module PushoutFlip = PushoutRec
    (right {d = Span-flip d})
    (left {d = Span-flip d})
    (λ z → ! (glue {d = Span-flip d} z))

  Pushout-flip : Pushout d → Pushout (Span-flip d)
  Pushout-flip = PushoutFlip.f

Pushout-flip-involutive : ∀ {i j k} (d : Span {i} {j} {k})
  (s : Pushout d) → Pushout-flip (Pushout-flip s) == s
Pushout-flip-involutive d = Pushout-elim
  (λ a → idp)
  (λ b → idp)
  (λ c → ↓-∘=idf-in' Pushout-flip Pushout-flip {p = glue c} $
     ap Pushout-flip (ap Pushout-flip (glue c))
       =⟨ ap (ap Pushout-flip) (PushoutFlip.glue-β c) ⟩
     ap Pushout-flip (! (glue c))
       =⟨ ap-! Pushout-flip (glue c) ⟩
     ! (ap Pushout-flip (glue c))
       =⟨ ap ! (PushoutFlip.glue-β c) ⟩
     ! (! (glue c))
       =⟨ !-! (glue c) ⟩
     glue c
       =∎)

{- Equivalence for spans with proofs that the equivalence swaps the
 - injections -}
Pushout-flip-equiv : ∀ {i j k} (d : Span {i} {j} {k})
  → Pushout d ≃ Pushout (Span-flip d)
Pushout-flip-equiv d =
  equiv Pushout-flip Pushout-flip
    (Pushout-flip-involutive (Span-flip d))
    (Pushout-flip-involutive d)
  where open Span d

module _ {i j k} (ps : ⊙Span {i} {j} {k}) where

  open ⊙Span ps

  private
    s = ⊙Span-to-Span ps

    preserves : –> (Pushout-flip-equiv s) (left (snd X)) == left (snd Y)
    preserves = snd (⊙right (⊙Span-flip ps))

  ⊙Pushout-flip : ⊙Pushout ps ⊙→ ⊙Pushout (⊙Span-flip ps)
  ⊙Pushout-flip = (PushoutFlip.f , preserves)

  {- action of [Pushout-flip] on [snd ⊙right] -}
  ap-Pushout-flip-right-pt : ap Pushout-flip (snd (⊙right ps))
          == ! (snd (⊙right (⊙Span-flip ps)))
  ap-Pushout-flip-right-pt = lemma f g
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
            (f : Z ⊙→ X) (g : Z ⊙→ Y)
          → ap (Pushout-flip {d = ⊙Span-to-Span (⊙span X Y Z f g)})
              (ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))
         == ! (ap right (! (snd f)) ∙ ! (glue (snd Z)) ∙' ap left (snd g))
    lemma {Z = Z} (f , idp) (g , idp) =
      ap Pushout-flip (! (glue (snd Z)))
        =⟨ ap-! Pushout-flip (glue (snd Z)) ⟩
      ! (ap Pushout-flip (glue (snd Z)))
        =⟨ PushoutFlip.glue-β (snd Z) |in-ctx ! ⟩
      ! (! (glue (snd Z)))
        =∎

module _ {i j k} (ps : ⊙Span {i} {j} {k}) where

  open ⊙Span ps

  ⊙Pushout-flip-involutive : ∀ {i j k} (ps : ⊙Span {i} {j} {k})
    → ⊙Pushout-flip (⊙Span-flip ps) ⊙∘ ⊙Pushout-flip ps == ⊙idf _
  ⊙Pushout-flip-involutive ps =
    ⊙λ= (Pushout-flip-involutive _) lemma
    where
    lemma :
      ap Pushout-flip (snd (⊙right (⊙Span-flip ps))) ∙ snd (⊙right ps)
      == idp
    lemma =
      ap Pushout-flip (snd (⊙right (⊙Span-flip ps))) ∙ snd (⊙right ps)
        =⟨ ap-Pushout-flip-right-pt (⊙Span-flip ps) |in-ctx _∙ snd (⊙right ps) ⟩
      ! (snd (⊙right ps)) ∙ snd (⊙right ps)
        =⟨ !-inv-l (snd (⊙right ps)) ⟩
      idp
        =∎
