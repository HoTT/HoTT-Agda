{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver

{- Flipping the pushout diagram (switching left and right) gives the
 - same pushout. -}

-- TODO XXX Establish naming conventions.

module cohomology.FlipPushout where

{- Span-flipping functions -}
flip-span : ∀ {i j k} → Span {i} {j} {k} → Span {j} {i} {k}
flip-span (span A B C f g) = span B A C g f

flip-⊙span : ∀ {i j k} → ⊙Span {i} {j} {k} → ⊙Span {j} {i} {k}
flip-⊙span (⊙span X Y Z f g) = ⊙span Y X Z g f

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
module _ {i j k} (ps : ⊙Span {i} {j} {k}) where

  open ⊙Span ps

  private
    s = ⊙span-out ps

    preserves : –> (flip-pushout-equiv s) (left (snd X)) == left (snd Y)
    preserves = snd (⊙right (flip-⊙span ps))

  flip-⊙pushout : fst (⊙Pushout ps ⊙→ ⊙Pushout (flip-⊙span ps))
  flip-⊙pushout = (FlipPushout.f , preserves)

  flip-⊙pushout-path : ⊙Pushout ps == ⊙Pushout (flip-⊙span ps)
  flip-⊙pushout-path = ⊙ua (≃-to-⊙≃ (flip-pushout-equiv s) preserves)

  {- action of [flip-pushout] on [snd ⊙right] -}
  ap-flip-right : ap flip-pushout (snd (⊙right ps))
               == ! (snd (⊙right (flip-⊙span ps)))
  ap-flip-right = lemma f g
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
        (f : fst (Z ⊙→ X)) (g : fst (Z ⊙→ Y))
      → ap (flip-pushout {d = ⊙span-out (⊙span X Y Z f g)})
          (ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))
        == ! (ap right (! (snd f)) ∙ ! (glue (snd Z)) ∙' ap left (snd g))
    lemma {Z = Z} (f , idp) (g , idp) =
      ap flip-pushout (! (glue (snd Z)))
        =⟨ ap-! flip-pushout (glue (snd Z)) ⟩
      ! (ap flip-pushout (glue (snd Z)))
        =⟨ FlipPushout.glue-β (snd Z) |in-ctx ! ⟩
      ! (! (glue (snd Z))) ∎

  flip-⊙left : ⊙left ps == ⊙right (flip-⊙span ps)
                  [ (λ W → fst (X ⊙→ W)) ↓ flip-⊙pushout-path ]
  flip-⊙left = codomain-over-⊙equiv _ _

  flip-⊙right : ⊙right ps == ⊙left (flip-⊙span ps)
                   [ (λ W → fst (Y ⊙→ W)) ↓ flip-⊙pushout-path ]
  flip-⊙right =
    codomain-over-⊙equiv _ _
    ▹ pair= idp (ap (λ w → w ∙ preserves) ap-flip-right ∙ !-inv-l preserves)

flip-⊙pushout-involutive : ∀ {i j k} (ps : ⊙Span {i} {j} {k})
  → flip-⊙pushout (flip-⊙span ps) ⊙∘ flip-⊙pushout ps == ⊙idf _
flip-⊙pushout-involutive ps =
  ⊙λ= (flip-pushout-involutive _) lemma
  where
  lemma :
    ap flip-pushout (snd (⊙right (flip-⊙span ps))) ∙ snd (⊙right ps)
    == idp
  lemma =
    ap flip-pushout (snd (⊙right (flip-⊙span ps))) ∙ snd (⊙right ps)
      =⟨ ap-flip-right (flip-⊙span ps)
         |in-ctx (λ w → w ∙ snd (⊙right ps)) ⟩
    ! (snd (⊙right ps)) ∙ snd (⊙right ps)
      =⟨ !-inv-l (snd (⊙right ps)) ⟩
    idp
