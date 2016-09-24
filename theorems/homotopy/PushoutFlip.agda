{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.FunctionOver

{- Flipping the pushout diagram (switching left and right) gives the
 - same pushout. -}

module homotopy.PushoutFlip where

{- Span-flipping functions -}
Span-flip : ∀ {i j k} → Span {i} {j} {k} → Span {j} {i} {k}
Span-flip (span A B C f g) = span B A C g f

⊙Span-flip : ∀ {i j k} → ⊙Span {i} {j} {k} → ⊙Span {j} {i} {k}
⊙Span-flip (⊙span X Y Z f g) = ⊙span Y X Z g f

{- Pushout-flipping function -}
module _ {i j k} {d : Span {i} {j} {k}} where

  module FlipPushout = PushoutRec
    (right {d = Span-flip d})
    (left {d = Span-flip d})
    (λ z → ! (glue {d = Span-flip d} z))

  Pushout-flip : Pushout d → Pushout (Span-flip d)
  Pushout-flip = FlipPushout.f

Pushout-flip-involutive : ∀ {i j k} (d : Span {i} {j} {k})
  (s : Pushout d) → Pushout-flip (Pushout-flip s) == s
Pushout-flip-involutive d = Pushout-elim
  (λ a → idp)
  (λ b → idp)
  (λ c → ↓-∘=idf-in Pushout-flip Pushout-flip $
     ap Pushout-flip (ap Pushout-flip (glue c))
       =⟨ ap (ap Pushout-flip) (FlipPushout.glue-β c) ⟩
     ap Pushout-flip (! (glue c))
       =⟨ ap-! Pushout-flip (glue c) ⟩
     ! (ap Pushout-flip (glue c))
       =⟨ ap ! (FlipPushout.glue-β c) ⟩
     ! (! (glue c))
       =⟨ !-! (glue c) ⟩
     glue c ∎)

{- Equivalence for spans with proofs that the equivalence swaps the
 - injections -}
module _ {i j k} (d : Span {i} {j} {k}) where

  open Span d

  Pushout-flip-equiv : Pushout d ≃ Pushout (Span-flip d)
  Pushout-flip-equiv =
    equiv Pushout-flip Pushout-flip
      (Pushout-flip-involutive (Span-flip d))
      (Pushout-flip-involutive d)

  Pushout-flip-path : Pushout d == Pushout (Span-flip d)
  Pushout-flip-path = ua Pushout-flip-equiv

  flip-left : left == right [ (λ D → (A → D)) ↓ Pushout-flip-path ]
  flip-left = codomain-over-equiv _ _

  flip-right : right == left [ (λ D → (B → D)) ↓ Pushout-flip-path ]
  flip-right = codomain-over-equiv _ _

{- Path for pointed spans with proofs that the path swaps the pointed
 - injections -}
module _ {i j k} (ps : ⊙Span {i} {j} {k}) where

  open ⊙Span ps

  private
    s = ⊙span-out ps

    preserves : –> (Pushout-flip-equiv s) (left (snd X)) == left (snd Y)
    preserves = snd (⊙right (⊙Span-flip ps))

  ⊙Pushout-flip : ⊙Pushout ps ⊙→ ⊙Pushout (⊙Span-flip ps)
  ⊙Pushout-flip = (FlipPushout.f , preserves)

  ⊙Pushout-flip-path : ⊙Pushout ps == ⊙Pushout (⊙Span-flip ps)
  ⊙Pushout-flip-path = ⊙ua (≃-to-⊙≃ (Pushout-flip-equiv s) preserves)

  {- action of [Pushout-flip] on [snd ⊙right] -}
  ap-flip-right : ap Pushout-flip (snd (⊙right ps))
               == ! (snd (⊙right (⊙Span-flip ps)))
  ap-flip-right = lemma f g
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
        (f : Z ⊙→ X) (g : Z ⊙→ Y)
      → ap (Pushout-flip {d = ⊙span-out (⊙span X Y Z f g)})
          (ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))
        == ! (ap right (! (snd f)) ∙ ! (glue (snd Z)) ∙' ap left (snd g))
    lemma {Z = Z} (f , idp) (g , idp) =
      ap Pushout-flip (! (glue (snd Z)))
        =⟨ ap-! Pushout-flip (glue (snd Z)) ⟩
      ! (ap Pushout-flip (glue (snd Z)))
        =⟨ FlipPushout.glue-β (snd Z) |in-ctx ! ⟩
      ! (! (glue (snd Z))) ∎

  -- XXX Naming convension
  flip-⊙left : ⊙left ps == ⊙right (⊙Span-flip ps)
                  [ (λ W → X ⊙→ W) ↓ ⊙Pushout-flip-path ]
  flip-⊙left = codomain-over-⊙equiv _ _

  -- XXX Naming convension
  flip-⊙right : ⊙right ps == ⊙left (⊙Span-flip ps)
                   [ (λ W → Y ⊙→ W) ↓ ⊙Pushout-flip-path ]
  flip-⊙right =
    codomain-over-⊙equiv _ _
    ▹ pair= idp (ap (λ w → w ∙ preserves) ap-flip-right ∙ !-inv-l preserves)

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
      =⟨ ap-flip-right (⊙Span-flip ps)
         |in-ctx (λ w → w ∙ snd (⊙right ps)) ⟩
    ! (snd (⊙right ps)) ∙ snd (⊙right ps)
      =⟨ !-inv-l (snd (⊙right ps)) ⟩
    idp
