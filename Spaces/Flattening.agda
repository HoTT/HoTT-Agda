{-# OPTIONS --without-K #-}

open import BaseOver

module Spaces.Flattening {i j k}
  (A : Set i) (B : Set j) (f g : B → A)
  (C : A → Set k) (D : (b : B) → C (f b) ≃ C (g b)) where

open import Spaces.FlatteningTypes A B f g C D

-- The family of paths used in the definition of [flatten]
paths-flatten : (b : B) → (cct (f b) ≡[ (λ w → (P w → Wt)) ↓ pp b ] cct (g b))
paths-flatten b =
  ↓-app→cst-in (λ q → ppt b _ ∘' ap (cct (g b)) (↓-pp-out q))

flatten-curried : (w : W) → (P w → Wt)
flatten-curried = W-rec _ cct paths-flatten

flatten : Σ W P → Wt
flatten (w , x) = flatten-curried w x

unflatten : Wt → Σ W P
unflatten = Wt-rec-nondep _ (λ a c → (cc a , c))
                            (λ b d → Σ-eq (pp b) (↓-pp-in refl))

--

flatten-unflatten : (w : Wt) → flatten (unflatten w) ≡ w
flatten-unflatten =
  Wt-rec _
    (λ _ _ → refl)
    (λ b d → ↓-◯≡id-in unflatten flatten
      (ap flatten (ap unflatten (ppt b d))
                 ≡⟨ Wt-rec-nondep-β _ (λ a c → (cc a , c)) (λ b d → Σ-eq (pp b) (↓-pp-in refl)) b d |in-ctx ap flatten ⟩
       ap flatten (Σ-eq (pp b) (↓-pp-in refl))
                 ≡⟨ split-ap2 flatten (pp b) (↓-pp-in refl) ⟩
       ↓-app→cst-out (apd flatten-curried (pp b)) (↓-pp-in refl)
                 ≡⟨ W-rec-β _ cct paths-flatten b |in-ctx (λ u → ↓-app→cst-out u (↓-pp-in refl)) ⟩
       ↓-app→cst-out (paths-flatten b) (↓-pp-in refl)
                 ≡⟨ refl ⟩
       ↓-app→cst-out (↓-app→cst-in
         (λ q → ppt b _ ∘' ap (cct (g b)) (↓-pp-out q))) (↓-pp-in refl)
                 ≡⟨ ↓-app→cst-β (λ q → ppt b _ ∘' ap (cct (g b)) (↓-pp-out q)) (↓-pp-in refl) ⟩
       ppt b d ∘' ap (cct (g b)) (↓-pp-out (↓-pp-in refl))
                 ≡⟨ ↓-pp-β refl |in-ctx (λ u → ppt b d ∘' ap (cct (g b)) u) ⟩
       ppt b d ∎))

unflatten-flatten-curried : (w : W) (x : P w)
  →  unflatten (flatten-curried w x) ≡ (w , x)
unflatten-flatten-curried =
  W-rec _ (λ a x → refl)
    (λ b → ↓-Π-in
    (λ q → ↓-◯≡id-in flatten unflatten
      (ap unflatten (ap flatten (Σ-eq (pp b) q))
                 ≡⟨ split-ap2 flatten (pp b) q |in-ctx ap unflatten ⟩
       ap unflatten (↓-app→cst-out (apd flatten-curried (pp b)) q)
                 ≡⟨ W-rec-β _ cct paths-flatten b |in-ctx (λ u → ap unflatten (↓-app→cst-out u q)) ⟩
       ap unflatten (↓-app→cst-out (paths-flatten b) q)
                 ≡⟨ refl ⟩
       ap unflatten (↓-app→cst-out (↓-app→cst-in (λ qq → ppt b _ ∘' ap (cct (g b)) (↓-pp-out qq))) q)
                 ≡⟨ ↓-app→cst-β (λ qq → ppt b _ ∘' ap (cct (g b)) (↓-pp-out qq)) q |in-ctx ap unflatten ⟩
       ap unflatten (ppt b _ ∘' ap (cct (g b)) (↓-pp-out q))
                 ≡⟨ ap-∘' unflatten (ppt b _) (ap (cct (g b)) (↓-pp-out q)) ⟩
       ap unflatten (ppt b _) ∘' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 ≡⟨ Wt-rec-nondep-β _ (λ a c → (cc a , c)) (λ b d → Σ-eq (pp b) (↓-pp-in refl)) b _ |in-ctx (λ u → u ∘' ap unflatten (ap (cct (g b)) (↓-pp-out q))) ⟩
       Σ-eq (pp b) (↓-pp-in refl) ∘' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 ≡⟨ compose-ap unflatten (cct (g b)) (↓-pp-out q) |in-ctx (λ u → (Σ-eq (pp b) (↓-pp-in refl) ∘' u)) ⟩
       Σ-eq (pp b) (↓-pp-in refl) ∘' ap (unflatten ◯ cct (g b)) (↓-pp-out q)
                 ≡⟨ refl ⟩
       Σ-eq (pp b) (↓-pp-in refl) ∘' ap (λ x → (cc (g b), x)) (↓-pp-out q)
                 ≡⟨ ap-cst,id P (↓-pp-out q) |in-ctx (λ u → Σ-eq (pp b) (↓-pp-in refl) ∘' u) ⟩
       Σ-eq (pp b) (↓-pp-in refl) ∘' Σ-eq refl (↓-pp-out q)
                 ≡⟨ Σ-∘' (↓-pp-in refl) (↓-pp-out q) ⟩
       Σ-eq (pp b) (↓-pp-in refl ∘'dep ↓-pp-out q)
                 ≡⟨ to-transp-weird q (pp-path _ _) |in-ctx Σ-eq (pp b) ⟩
       Σ-eq (pp b) q ∎)))

unflatten-flatten : (wx : Σ W P) → unflatten (flatten wx) ≡ wx
unflatten-flatten (w , x) = unflatten-flatten-curried w x

eqv : Σ W P ≃ Wt
eqv = (flatten , iso-is-eq flatten unflatten flatten-unflatten unflatten-flatten)
