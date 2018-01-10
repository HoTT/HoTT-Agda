{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

{-
This file contains various lemmas that rely on lib.types.Paths or
functional extensionality for pointed maps.
-}

module lib.types.Pointed where

{- Pointed maps -}

⊙app= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f == g → f ⊙∼ g
⊙app= {X = X} {Y = Y} p =
  app= (fst= p) , ↓-ap-in (_== pt Y) (λ u → u (pt X)) (snd= p)

-- function extensionality for pointed maps
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f ⊙∼ g → f == g
⊙λ= {g = g} (p , α) = pair= (λ= p)
  (↓-app=cst-in (↓-idf=cst-out α ∙ ap (_∙ snd g) (! (app=-β p _))))

⊙λ=' : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  (p : fst f ∼ fst g)
  (α : snd f == snd g [ (λ y → y == pt Y) ↓ p (pt X) ])
  → f == g
⊙λ=' {g = g} = curry ⊙λ=

-- associativity of pointed maps
⊙∘-assoc-pt : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {a₁ a₂ : A} (f : A → B) {b : B} (g : B → C) {c : C}
  (p : a₁ == a₂) (q : f a₂ == b) (r : g b == c)
  → ⊙∘-pt (g ∘ f) p (⊙∘-pt g q r) == ⊙∘-pt g (⊙∘-pt f p q) r
⊙∘-assoc-pt _ _ idp _ _ = idp

⊙∘-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ((h ⊙∘ g) ⊙∘ f) ⊙∼ (h ⊙∘ (g ⊙∘ f))
⊙∘-assoc (h , hpt) (g , gpt) (f , fpt) = (λ _ → idp) , ⊙∘-assoc-pt g h fpt gpt hpt

⊙∘-cst-l : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : X ⊙→ Y) → (⊙cst :> (Y ⊙→ Z)) ⊙∘ f ⊙∼ ⊙cst
⊙∘-cst-l {Z = Z} f = (λ _ → idp) , ap (_∙ idp) (ap-cst (pt Z) (snd f))

⊙∘-cst-r : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : Y ⊙→ Z) → f ⊙∘ (⊙cst :> (X ⊙→ Y)) ⊙∼ ⊙cst
⊙∘-cst-r {X = X} f = (λ _ → snd f) , ↓-idf=cst-in' idp

{- Pointed equivalences -}

-- Extracting data from an pointed equivalence
module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  ⊙≃-to-≃ : de⊙ X ≃ de⊙ Y
  ⊙≃-to-≃ = fst (fst ⊙e) , snd ⊙e

  ⊙–> : X ⊙→ Y
  ⊙–> = fst ⊙e

  ⊙–>-pt = snd ⊙–>

  ⊙<– : Y ⊙→ X
  ⊙<– = is-equiv.g (snd ⊙e) , lemma ⊙e where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y) → is-equiv.g (snd ⊙e) (pt Y) == pt X
    lemma ((f , idp) , f-ise) = is-equiv.g-f f-ise (pt X)

  ⊙<–-pt = snd ⊙<–

  infix 120 _⊙⁻¹
  _⊙⁻¹ : Y ⊙≃ X
  _⊙⁻¹ = ⊙<– , is-equiv-inverse (snd ⊙e)

module _ {i j} {X : Ptd i} {Y : Ptd j} where 

  ⊙<–-inv-l : (⊙e : X ⊙≃ Y) → ⊙<– ⊙e ⊙∘ ⊙–> ⊙e ⊙∼ ⊙idf _
  ⊙<–-inv-l ⊙e = <–-inv-l (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙<– ⊙e ⊙∘ ⊙–> ⊙e) == is-equiv.g-f (snd ⊙e) (pt X)
    lemma ((f , idp) , f-ise) = idp

  ⊙<–-inv-r : (⊙e : X ⊙≃ Y) → ⊙–> ⊙e ⊙∘ ⊙<– ⊙e ⊙∼ ⊙idf _
  ⊙<–-inv-r ⊙e = <–-inv-r (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙–> ⊙e ⊙∘ ⊙<– ⊙e) == is-equiv.f-g (snd ⊙e) (pt Y)
    lemma ((f , idp) , f-ise) = ∙-unit-r _ ∙ is-equiv.adj f-ise (pt X)

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (⊙e : X ⊙≃ Y) where

  post⊙∘-is-equiv : is-equiv (λ (k : Z ⊙→ X) → ⊙–> ⊙e ⊙∘ k)
  post⊙∘-is-equiv = is-eq (⊙–> ⊙e ⊙∘_) (⊙<– ⊙e ⊙∘_) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : ∀ {Y} (⊙e : X ⊙≃ Y) (k : Z ⊙→ Y) → ⊙–> ⊙e ⊙∘ (⊙<– ⊙e ⊙∘ k) == k
      to-from ((f , idp) , f-ise) (k , k-pt) = ⊙λ=' (f.f-g ∘ k) (↓-idf=cst-in' $ lemma k-pt)
        where
          module f = is-equiv f-ise
          lemma : ∀ {y₀} (k-pt : y₀ == f (pt X))
            → ⊙∘-pt f (⊙∘-pt f.g k-pt (f.g-f _)) idp == f.f-g y₀ ∙' k-pt
          lemma idp = ∙-unit-r _ ∙ f.adj _

      from-to : ∀ {Y} (⊙e : X ⊙≃ Y) (k : Z ⊙→ X) → ⊙<– ⊙e ⊙∘ (⊙–> ⊙e ⊙∘ k) == k
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (f.g-f ∘ k) $ ↓-idf=cst-in' idp
        where module f = is-equiv f-ise

  post⊙∘-equiv : (Z ⊙→ X) ≃ (Z ⊙→ Y)
  post⊙∘-equiv = _ , post⊙∘-is-equiv

  pre⊙∘-is-equiv : is-equiv (λ (k : Y ⊙→ Z) → k ⊙∘ ⊙–> ⊙e)
  pre⊙∘-is-equiv = is-eq (_⊙∘ ⊙–> ⊙e) (_⊙∘ ⊙<– ⊙e) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : ∀ {Z} (⊙e : X ⊙≃ Y) (k : X ⊙→ Z) → (k ⊙∘ ⊙<– ⊙e) ⊙∘ ⊙–> ⊙e == k
      to-from ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.g-f) $ ↓-idf=cst-in' $ ∙-unit-r _
        where module f = is-equiv f-ise

      from-to : ∀ {Z} (⊙e : X ⊙≃ Y) (k : Y ⊙→ Z) → (k ⊙∘ ⊙–> ⊙e) ⊙∘ ⊙<– ⊙e == k
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.f-g) $ ↓-idf=cst-in' $
        ∙-unit-r _ ∙ ap-∘ k f (f.g-f (pt X)) ∙ ap (ap k) (f.adj (pt X))
        where module f = is-equiv f-ise

  pre⊙∘-equiv : (Y ⊙→ Z) ≃ (X ⊙→ Z)
  pre⊙∘-equiv = _ , pre⊙∘-is-equiv

{- Pointed maps out of bool -}

-- intuition : [f true] is fixed and the only changable part is [f false].

⊙Bool→-to-idf : ∀ {i} {X : Ptd i}
  → ⊙Bool ⊙→ X → de⊙ X
⊙Bool→-to-idf (h , _) = h false

⊙Bool→-equiv-idf : ∀ {i} (X : Ptd i)
  → (⊙Bool ⊙→ X) ≃ de⊙ X
⊙Bool→-equiv-idf {i} X = equiv ⊙Bool→-to-idf g f-g g-f
  where
  g : de⊙ X → ⊙Bool ⊙→ X
  g x = Bool-rec (pt X) x , idp

  abstract
    f-g : ∀ x → ⊙Bool→-to-idf (g x) == x
    f-g x = idp

    g-f : ∀ H → g (⊙Bool→-to-idf H) == H
    g-f (h , hpt) = pair=
      (λ= lemma)
      (↓-app=cst-in $
        idp
          =⟨ ! (!-inv-l hpt) ⟩
        ! hpt ∙ hpt
          =⟨ ! (app=-β lemma true) |in-ctx (λ w → w ∙ hpt) ⟩
        app= (λ= lemma) true ∙ hpt
          =∎)
      where lemma : ∀ b → fst (g (h false)) b == h b
            lemma true = ! hpt
            lemma false = idp
