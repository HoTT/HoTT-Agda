{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.Flattening {i j k}
  (A : Type i) (B : Type j) (f g : B → A)
  (C : A → Type k) (D : (b : B) → C (f b) ≃ C (g b)) where

open import homotopy.FlatteningTypes A B f g C D

-- The family of paths used in the definition of [flatten]
paths-flatten : (b : B) → (cct (f b) == cct (g b) [ (λ w → (P w → Wt)) ↓ pp b ])
paths-flatten b =
  ↓-app→cst-in (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))

flatten-curried : (w : W) → (P w → Wt)
flatten-curried = W-elim cct paths-flatten

flatten : Σ W P → Wt
flatten (w , x) = flatten-curried w x

unflatten : Wt → Σ W P
unflatten = Wt-rec (λ a c → (cc a , c))
                            (λ b d → pair= (pp b) (↓-pp-in idp))

--

flatten-unflatten : (w : Wt) → flatten (unflatten w) == w
flatten-unflatten =
  Wt-elim
    (λ _ _ → idp)
    (λ b d → ↓-∘=id-in unflatten flatten
      (ap flatten (ap unflatten (ppt b d))
                 =⟨ ppt-β' (λ a c → (cc a , c)) (λ b d → pair= (pp b) (↓-pp-in idp)) b d |in-ctx ap flatten ⟩
       ap flatten (pair= (pp b) (↓-pp-in idp))
                 =⟨ split-ap2 flatten (pp b) (↓-pp-in idp) ⟩
       ↓-app→cst-out (apd flatten-curried (pp b)) (↓-pp-in idp)
                 =⟨ pp-β cct paths-flatten b |in-ctx (λ u → ↓-app→cst-out u (↓-pp-in idp)) ⟩
       ↓-app→cst-out (paths-flatten b) (↓-pp-in idp)
                 =⟨ idp ⟩
       ↓-app→cst-out (↓-app→cst-in
         (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))) (↓-pp-in idp)
                 =⟨ ↓-app→cst-β (λ q → ppt b _ ∙' ap (cct (g b)) (↓-pp-out q)) (↓-pp-in idp) ⟩
       ppt b d ∙' ap (cct (g b)) (↓-pp-out (↓-pp-in idp))
                 =⟨ ↓-pp-β idp |in-ctx (λ u → ppt b d ∙' ap (cct (g b)) u) ⟩
       ppt b d ∎))

unflatten-flatten-curried : (w : W) (x : P w)
  →  unflatten (flatten-curried w x) == (w , x)
unflatten-flatten-curried =
  W-elim (λ a x → idp)
    (λ b → ↓-Π-in
    (λ q → ↓-∘=id-in flatten unflatten
      (ap unflatten (ap flatten (pair= (pp b) q))
                 =⟨ split-ap2 flatten (pp b) q |in-ctx ap unflatten ⟩
       ap unflatten (↓-app→cst-out (apd flatten-curried (pp b)) q)
                 =⟨ pp-β cct paths-flatten b |in-ctx (λ u → ap unflatten (↓-app→cst-out u q)) ⟩
       ap unflatten (↓-app→cst-out (paths-flatten b) q)
                 =⟨ idp ⟩
       ap unflatten (↓-app→cst-out (↓-app→cst-in (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq))) q)
                 =⟨ ↓-app→cst-β (λ qq → ppt b _ ∙' ap (cct (g b)) (↓-pp-out qq)) q |in-ctx ap unflatten ⟩
       ap unflatten (ppt b _ ∙' ap (cct (g b)) (↓-pp-out q))
                 =⟨ ap-∙' unflatten (ppt b _) (ap (cct (g b)) (↓-pp-out q)) ⟩
       ap unflatten (ppt b _) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 =⟨ ppt-β' (λ a c → (cc a , c)) (λ b d → pair= (pp b) (↓-pp-in idp)) b _ |in-ctx (λ u → u ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap unflatten (ap (cct (g b)) (↓-pp-out q))
                 =⟨ ∘-ap unflatten (cct (g b)) (↓-pp-out q) |in-ctx (λ u → (pair= (pp b) (↓-pp-in idp) ∙' u)) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap (unflatten ∘ cct (g b)) (↓-pp-out q)
                 =⟨ idp ⟩
       pair= (pp b) (↓-pp-in idp) ∙' ap (λ x → (cc (g b), x)) (↓-pp-out q)
                 =⟨ ap-cst,id P (↓-pp-out q) |in-ctx (λ u → pair= (pp b) (↓-pp-in idp) ∙' u) ⟩
       pair= (pp b) (↓-pp-in idp) ∙' pair= idp (↓-pp-out q)
                 =⟨ Σ-∙' (↓-pp-in idp) (↓-pp-out q) ⟩
       pair= (pp b) (↓-pp-in idp ∙'dep ↓-pp-out q)
                 =⟨ to-transp-weird q (pp-path _ _) |in-ctx pair= (pp b) ⟩
       pair= (pp b) q ∎)))

unflatten-flatten : (wx : Σ W P) → unflatten (flatten wx) == wx
unflatten-flatten (w , x) = unflatten-flatten-curried w x

eqv : Σ W P ≃ Wt
eqv = equiv flatten unflatten flatten-unflatten unflatten-flatten
