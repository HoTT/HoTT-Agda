{-# OPTIONS --without-K #-}

open import Base

module Homotopy.Pushout where

open import Homotopy.PushoutDef public

pushout-diag-flip : ∀ {i} → pushout-diag i → pushout-diag i
pushout-diag-flip (diag A , B , C , f , g) = diag B , A , C , g , f

pushout-flip : ∀ {i} {d : pushout-diag i} → pushout d → pushout (pushout-diag-flip d)
pushout-flip {d = d} = pushout-rec-nondep
  (pushout $ pushout-diag-flip d)
  right left (! ◯ glue)

pushout-flip-flip : ∀ {i} {d : pushout-diag i} (p : pushout d)
                    → pushout-flip (pushout-flip p) ≡ p
pushout-flip-flip {d = d} = pushout-rec
  (λ p → pushout-flip (pushout-flip p) ≡ p)
  (λ _ → refl)
  (λ _ → refl)
  (λ c →
    transport (λ p → pushout-flip (pushout-flip p) ≡ p) (glue c) refl
      ≡⟨ trans-app≡id (pushout-flip ◯ pushout-flip) (glue c) refl ⟩
    ! (ap (pushout-flip ◯ pushout-flip) (glue c)) ∘ glue c
      ≡⟨ ap (λ x → ! x ∘ glue c)
            $ ap-compose pushout-flip pushout-flip (glue c) ⟩
    ! (ap pushout-flip (ap pushout-flip (glue c))) ∘ glue c
      ≡⟨ ap (λ x → ! (ap pushout-flip x) ∘ glue c)
            $ pushout-β-glue-nondep (pushout $ pushout-diag-flip d) right left (! ◯ glue) c ⟩
    ! (ap pushout-flip (! (glue c))) ∘ glue c
      ≡⟨ ap (λ x → ! x ∘ glue c) $ ap-opposite pushout-flip (glue c) ⟩
    ! (! (ap pushout-flip (glue c))) ∘ glue c
      ≡⟨ ap (λ x → ! (! x) ∘ glue c)
            $ pushout-β-glue-nondep (pushout d) right left (! ◯ glue) c ⟩
    ! (! (! (glue c))) ∘ glue c
      ≡⟨ ap (λ x → ! x ∘ glue c) $ opposite-opposite $ glue c ⟩
    ! (glue c) ∘ glue c
      ≡⟨ opposite-left-inverse (glue c) ⟩∎
    refl
      ∎)

pushout-β-!glue-nondep : ∀ {i} {d : pushout-diag i} {l} (D : Set l) →
  let open pushout-diag d in
  (left* : A → D) (right* : B → D)
  (glue* : (c : C) → left* (f c) ≡ right* (g c)) (c : C)
  → ap (pushout-rec-nondep D left* right* glue*) (! (glue c)) ≡ ! (glue* c)
pushout-β-!glue-nondep D left* right* glue* c =
  ap (pushout-rec-nondep D left* right* glue*) (! (glue c))
    ≡⟨ ap-opposite (pushout-rec-nondep D left* right* glue*) $ glue c ⟩
  ! (ap (pushout-rec-nondep D left* right* glue*) $ glue c)
    ≡⟨ ap ! $ pushout-β-glue-nondep D left* right* glue* c ⟩∎
  ! (glue* c)
    ∎
