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
  (λ c → ↓-app=idf-in $
    idp ∙' glue c
      =⟨ ∙'-unit-l _ ⟩
    glue c
      =⟨ ! (!-! (glue c)) ⟩
    ! (! (glue c))
      =⟨ ap ! (! (FlipPushout.glue-β c)) ⟩
    ! (ap flip-pushout (glue c))
      =⟨ !-ap flip-pushout (glue c) ⟩
    ap flip-pushout (! (glue c))
      =⟨ ! (FlipPushout.glue-β c) |in-ctx (λ w → ap flip-pushout w) ⟩
    ap flip-pushout (ap flip-pushout (glue c))
      =⟨ ∘-ap flip-pushout flip-pushout (glue c) ⟩
    ap (flip-pushout ∘ flip-pushout) (glue c)
      =⟨ ! (∙-unit-r _) ⟩
    ap (flip-pushout ∘ flip-pushout) (glue c) ∙ idp ∎)

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
    preserves = snd (ptd-right {d = flip-ptd-span ps})

  flip-ptd-pushout : fst (Ptd-Pushout ps ∙→ Ptd-Pushout (flip-ptd-span ps))
  flip-ptd-pushout = (FlipPushout.f , preserves)

  flip-ptd-pushout-path : Ptd-Pushout ps == Ptd-Pushout (flip-ptd-span ps)
  flip-ptd-pushout-path = ptd-ua (flip-pushout-equiv s) preserves

  flip-ptd-left : ptd-left {d = ps} == ptd-right {d = flip-ptd-span ps}
                  [ (λ W → fst (X ∙→ W)) ↓ flip-ptd-pushout-path ]
  flip-ptd-left = codomain-over-ptd-equiv _ _ _

  flip-ptd-right : ptd-right {d = ps} == ptd-left {d = flip-ptd-span ps}
                   [ (λ W → fst (Y ∙→ W)) ↓ flip-ptd-pushout-path ]
  flip-ptd-right =
    codomain-over-ptd-equiv _ _ _ ▹ pair= idp (lemma f g)
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
      (f : fst (Z ∙→ X)) (g : fst (Z ∙→ Y))
      → ap flip-pushout
          (ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))
        ∙ (ap right (! (snd f)) ∙ ! (glue (snd Z)) ∙' ap left (snd g))
        == idp
    lemma {Z = Z} (f , idp) (g , idp) = 
      ap flip-pushout (! (glue (snd Z))) ∙ ! (glue (snd Z))
         =⟨ ap-! flip-pushout (glue (snd Z))
            |in-ctx (λ w → w ∙ ! (glue (snd Z))) ⟩
      ! (ap flip-pushout (glue (snd Z))) ∙ ! (glue (snd Z))
         =⟨ FlipPushout.glue-β (snd Z)
            |in-ctx (λ w → ! w ∙ ! (glue (snd Z))) ⟩
      ! (! (glue (snd Z))) ∙ ! (glue (snd Z))
         =⟨ !-inv-l (! (glue (snd Z))) ⟩
      idp ∎
      
