{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.CubeMove

module lib.cubical.elims.CofWedge where

cof-wedge-path-elim : ∀ {i j k l}
  {X : Ptd i} {Y : Ptd j} {C : Type k} {D : Type l}
  {f : Wedge X Y → C} (g h : Cofiber f → D)
  → (p : g (cfbase _) == h (cfbase _))
  → (q : (c : C) → g (cfcod _ c) == h (cfcod _ c))
  → ((x : fst X) → Square p (ap g (cfglue _ (winl x)))
                            (ap h (cfglue _ (winl x))) (q (f (winl x))))
  → ((y : fst Y) → Square p (ap g (cfglue _ (winr y)))
                            (ap h (cfglue _ (winr y))) (q (f (winr y))))
  → ((κ : Cofiber f) → g κ == h κ)
cof-wedge-path-elim {X = X} {Y = Y} {f = f} g h base* cod* winl* winr* =
  Cofiber-elim _
    base*
    cod*
    (↓-='-from-square ∘ Wedge-elim
      winl*
      (λ y → fst fill ⊡h winr* y)
      (cube-to-↓-square $
        cube-right-from-front _ (winr* (snd Y)) (snd fill)))
  where
  fill : Σ (Square base* idp idp base*) (λ sq' →
    Cube (winl* (snd X)) sq'
      (natural-square (λ _ → base*) wglue)
      (square-push-rb _ _ (natural-square (ap g ∘ cfglue _) wglue))
      (square-push-rb _ _ (natural-square (ap h ∘ cfglue _) wglue))
      (natural-square (cod* ∘ f) wglue ⊡h' !□h (winr* (snd Y))))

  fill = fill-cube-right _ _ _ _ _

{- Note, only squares with constant endpoints. General case? -}
cof-wedge-square-elim : ∀ {i j k l}
  {X : Ptd i} {Y : Ptd j} {C : Type k} {D : Type l}
  {f : Wedge X Y → C} {d₀₀ d₀₁ d₁₀ d₁₁ : D}
  (p₀₋ : (κ : Cofiber f) → d₀₀ == d₀₁)
  (p₋₀ : (κ : Cofiber f) → d₀₀ == d₁₀)
  (p₋₁ : (κ : Cofiber f) → d₀₁ == d₁₁)
  (p₁₋ : (κ : Cofiber f) → d₁₀ == d₁₁)
  → (base* : Square (p₀₋ (cfbase _)) (p₋₀ (cfbase _))
                    (p₋₁ (cfbase _)) (p₁₋ (cfbase _)))
  → (cod* : (c : C) → Square (p₀₋ (cfcod _ c)) (p₋₀ (cfcod _ c))
                             (p₋₁ (cfcod _ c)) (p₁₋ (cfcod _ c)))
  → ((x : fst X) → Cube base* (cod* (f (winl x)))
                     (natural-square p₀₋ (cfglue _ (winl x)))
                     (natural-square p₋₀ (cfglue _ (winl x)))
                     (natural-square p₋₁ (cfglue _ (winl x)))
                     (natural-square p₁₋ (cfglue _ (winl x))))
  → ((y : fst Y) → Cube base* (cod* (f (winr y)))
                     (natural-square p₀₋ (cfglue _ (winr y)))
                     (natural-square p₋₀ (cfglue _ (winr y)))
                     (natural-square p₋₁ (cfglue _ (winr y)))
                     (natural-square p₁₋ (cfglue _ (winr y))))

  → ((κ : Cofiber f) → Square (p₀₋ κ) (p₋₀ κ) (p₋₁ κ) (p₁₋ κ))
cof-wedge-square-elim p₀₋ p₋₀ p₋₁ p₁₋ base* cod* winl* winr* =
  disc-to-square ∘ cof-wedge-path-elim _ _
    (square-to-disc base*)
    (square-to-disc ∘ cod*)
    (cube-to-disc-square ∘ winl*)
    (cube-to-disc-square ∘ winr*)
