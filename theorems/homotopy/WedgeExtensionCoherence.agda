{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.WedgeExtension

module homotopy.WedgeExtensionCoherence {i}
  {A : Type i} {a₀ : A}
  {B : Type i} {b₀ : B}
  {C : Type i} {c₀ : C}
  (A-is-0-connected : is-connected 0 A)
  (B-is-0-connected : is-connected 0 B)
  (C-is-0-connected : is-connected 0 C)
  (P : A → B → C → 0 -Type i)
  (f : (a : A) → fst (P a b₀ c₀))
  (g : (b : B) → fst (P a₀ b c₀))
  (h : (c : C) → fst (P a₀ b₀ c))
  (p : f a₀ == g b₀)
  (q : g b₀ == h c₀)
    where

  f-g-ext-args : args {i} {i} {A} {a₀} {B} {b₀}
  f-g-ext-args =
    record {
      n = -1; m = -1;
      cA = A-is-0-connected;
      cB = B-is-0-connected;
      P = λ a b → P a b c₀;
      f = f;
      g = g;
      p = p
    }

  f-g-ext : ∀ a b → fst (P a b c₀)
  f-g-ext = ext f-g-ext-args

  fg-h-ext-args : args {i} {i} {A × B} {a₀ , b₀} {C} {c₀}
  fg-h-ext-args =
    record {
      n = -1; m = -1;
      cA = ×-conn A-is-0-connected B-is-0-connected;
      cB = C-is-0-connected;
      P = λ s c → P (fst s) (snd s) c;
      f = λ s → f-g-ext (fst s) (snd s);
      g = h;
      p = β-r {r = f-g-ext-args} b₀ ∙ q
    }

  fg-h-ext : ∀ a b c → fst (P a b c)
  fg-h-ext a b c = ext fg-h-ext-args (a , b) c

  g-h-ext-args : args {i} {i} {B} {b₀} {C} {c₀}
  g-h-ext-args =
    record {
      n = -1; m = -1;
      cA = B-is-0-connected;
      cB = C-is-0-connected;
      P = λ b c → P a₀ b c;
      f = g;
      g = h;
      p = q
    }

  g-h-ext : ∀ b c → fst (P a₀ b c)
  g-h-ext = ext g-h-ext-args

  f-gh-ext-args : args {i} {i} {A} {a₀} {B × C} {b₀ , c₀}
  f-gh-ext-args =
    record {
      n = -1; m = -1;
      cA = A-is-0-connected;
      cB = ×-conn B-is-0-connected C-is-0-connected;
      P = λ a t → P a (fst t) (snd t);
      f = f;
      g = λ t → g-h-ext (fst t) (snd t);
      p = p ∙ ! (β-l {r = g-h-ext-args} b₀)
    }

  f-gh-ext : ∀ a b c → fst (P a b c)
  f-gh-ext a b c = ext f-gh-ext-args a (b , c)

  ext-coh : ∀ a b c → fg-h-ext a b c == f-gh-ext a b c
  ext-coh =
    prop-over-connected {a = a₀} {{A-is-0-connected}}
                        (λ a → (∀ b c → P' a b c) , Π-level (λ b → Π-level (P'-is-prop a b))) $
    prop-over-connected {a = b₀} {{B-is-0-connected}}
                        (λ b → (∀ c → P' a₀ b c) , Π-level (P'-is-prop a₀ b))
                        eq
    where
    P' : (a : A) (b : B) (c : C) → Type i
    P' a b c = fg-h-ext a b c == f-gh-ext a b c
    P'-is-prop : ∀ a b c → is-prop (P' a b c)
    P'-is-prop a b c = has-level-apply (snd (P a b c)) _ _
    eq : ∀ c → fg-h-ext a₀ b₀ c == f-gh-ext a₀ b₀ c
    eq c =
      fg-h-ext a₀ b₀ c
        =⟨ β-r {r = fg-h-ext-args} c ⟩
      h c
        =⟨ ! (β-r {r = g-h-ext-args} c) ⟩
      g-h-ext b₀ c
        =⟨ ! (β-r {r = f-gh-ext-args} (b₀ , c)) ⟩
      f-gh-ext a₀ b₀ c =∎
