{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver

{- Flipping the pushout diagram (switching left and right) gives the
 - same pushout. -}

module cohomology.FlipPushout where

{- Span-flipping functions -}
flip-span : ∀ {i j k} → Span {i} {j} {k} → Span {j} {i} {k}
flip-span (span A B C f g) = span B A C g f

flip-ptd-span : ∀ {i j k} → Ptd-Span {i} {j} {k} → Ptd-Span {j} {i} {k}
flip-ptd-span (ptd-span X Y Z f g) = ptd-span Y X Z g f

{- Pushout-flipping function -}
module _ {i j k} {d : Span {i} {j} {k}} where

  module FlipPushout = PushoutRec
    (right {d = flip-span d})
    (left {d = flip-span d})
    (λ z → ! (glue {d = flip-span d} z))

  flip-pushout : Pushout d → Pushout (flip-span d)
  flip-pushout = FlipPushout.f

flip-pushout-involutive : ∀ {i j k} (d : Span {i} {j} {k})
  (s : Pushout d) → flip-pushout (flip-pushout s) == s
flip-pushout-involutive d = Pushout-elim
  (λ a → idp)
  (λ b → idp)
  (λ c → ↓-∘=idf-in flip-pushout flip-pushout $
     ap flip-pushout (ap flip-pushout (glue c))
       =⟨ ap (ap flip-pushout) (FlipPushout.glue-β c) ⟩
     ap flip-pushout (! (glue c))
       =⟨ ap-! flip-pushout (glue c) ⟩
     ! (ap flip-pushout (glue c))
       =⟨ ap ! (FlipPushout.glue-β c) ⟩
     ! (! (glue c))
       =⟨ !-! (glue c) ⟩
     glue c ∎)

{- Equivalence for spans with proofs that the equivalence swaps the
 - injections -}
module _ {i j k} (d : Span {i} {j} {k}) where

  open Span d

  flip-pushout-equiv : Pushout d ≃ Pushout (flip-span d)
  flip-pushout-equiv =
    equiv flip-pushout flip-pushout
      (flip-pushout-involutive (flip-span d))
      (flip-pushout-involutive d)

  flip-pushout-path : Pushout d == Pushout (flip-span d)
  flip-pushout-path = ua flip-pushout-equiv

  flip-left : left == right [ (λ D → (A → D)) ↓ flip-pushout-path ]
  flip-left = codomain-over-equiv _ _

  flip-right : right == left [ (λ D → (B → D)) ↓ flip-pushout-path ]
  flip-right = codomain-over-equiv _ _

{- Path for pointed spans with proofs that the path swaps the pointed
 - injections -}
module _ {i j k} (ps : Ptd-Span {i} {j} {k}) where

  open Ptd-Span ps

  private
    s = ptd-span-out ps

    preserves : –> (flip-pushout-equiv s) (left (snd X)) == left (snd Y)
    preserves = snd (ptd-right (flip-ptd-span ps))

  flip-ptd-pushout : fst (Ptd-Pushout ps ∙→ Ptd-Pushout (flip-ptd-span ps))
  flip-ptd-pushout = (FlipPushout.f , preserves)

  flip-ptd-pushout-path : Ptd-Pushout ps == Ptd-Pushout (flip-ptd-span ps)
  flip-ptd-pushout-path = ptd-ua (flip-pushout-equiv s) preserves

  {- action of [flip-pushout] on [snd ptd-right] -}
  ap-flip-right : ap flip-pushout (snd (ptd-right ps))
               == ! (snd (ptd-right (flip-ptd-span ps)))
  ap-flip-right = lemma f g
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
        (f : fst (Z ∙→ X)) (g : fst (Z ∙→ Y))
      → ap (flip-pushout {d = ptd-span-out (ptd-span X Y Z f g)})
          (ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))
        == ! (ap right (! (snd f)) ∙ ! (glue (snd Z)) ∙' ap left (snd g))
    lemma {Z = Z} (f , idp) (g , idp) =
      ap flip-pushout (! (glue (snd Z)))
        =⟨ ap-! flip-pushout (glue (snd Z)) ⟩
      ! (ap flip-pushout (glue (snd Z)))
        =⟨ FlipPushout.glue-β (snd Z) |in-ctx ! ⟩
      ! (! (glue (snd Z))) ∎

  flip-ptd-left : ptd-left ps == ptd-right (flip-ptd-span ps)
                  [ (λ W → fst (X ∙→ W)) ↓ flip-ptd-pushout-path ]
  flip-ptd-left = codomain-over-ptd-equiv _ _ _

  flip-ptd-right : ptd-right ps == ptd-left (flip-ptd-span ps)
                   [ (λ W → fst (Y ∙→ W)) ↓ flip-ptd-pushout-path ]
  flip-ptd-right =
    codomain-over-ptd-equiv _ _ _
    ▹ pair= idp (ap (λ w → w ∙ preserves) ap-flip-right ∙ !-inv-l preserves)

flip-ptd-pushout-involutive : ∀ {i j k} (ps : Ptd-Span {i} {j} {k})
  → flip-ptd-pushout (flip-ptd-span ps) ∘ptd flip-ptd-pushout ps == ptd-idf _
flip-ptd-pushout-involutive ps =
  ptd-λ= (flip-pushout-involutive _) lemma
  where
  lemma :
    ap flip-pushout (snd (ptd-right (flip-ptd-span ps))) ∙ snd (ptd-right ps)
    == idp
  lemma =
    ap flip-pushout (snd (ptd-right (flip-ptd-span ps))) ∙ snd (ptd-right ps)
      =⟨ ap-flip-right (flip-ptd-span ps)
         |in-ctx (λ w → w ∙ snd (ptd-right ps)) ⟩
    ! (snd (ptd-right ps)) ∙ snd (ptd-right ps)
      =⟨ !-inv-l (snd (ptd-right ps)) ⟩
    idp
