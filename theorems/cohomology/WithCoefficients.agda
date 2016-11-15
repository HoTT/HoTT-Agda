{-# OPTIONS --without-K #-}

open import HoTT

-- TODO Is it possible to have a more generic [→-group] construction?

module cohomology.WithCoefficients where

⊙→Ω-group-structure : ∀ {i j} (X : Ptd i) (Y : Ptd j)
  → GroupStructure (X ⊙→ ⊙Ω Y)
⊙→Ω-group-structure X Y = record {
  ident = ⊙cst;
  inv = λ F → ((! ∘ fst F) , ap ! (snd F));
  comp = λ F G → ⊙Ω-∙ ⊙∘ ⊙fanout F G;
  unit-l = λ G → ⊙λ= (λ _ → idp) (unit-l-lemma (snd G));
  unit-r = λ F → ⊙λ= (∙-unit-r ∘ fst F) (unit-r-lemma (snd F));
  assoc = λ F G H → ⊙λ=
    (λ x → ∙-assoc (fst F x) (fst G x) (fst H x))
    (assoc-lemma (snd F) (snd G) (snd H));
  inv-l = λ F → ⊙λ= (!-inv-l ∘ fst F) (inv-l-lemma (snd F));
  inv-r = λ F → ⊙λ= (!-inv-r ∘ fst F) (inv-r-lemma (snd F))}
  where

  unit-l-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt idp α) idp == α
  unit-l-lemma idp = idp

  unit-r-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α idp) idp == α [ _== idp ↓ ∙-unit-r p ]
  unit-r-lemma idp = idp

  assoc-lemma : ∀ {i} {A : Type i} {x : A} {p q r : x == x}
    (α : p == idp) (β : q == idp) (γ : r == idp)
    →  ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt (⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α β) idp) γ) idp
    == ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α (⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt β γ) idp)) idp
     [ _== idp ↓ ∙-assoc p q r ]
  assoc-lemma idp idp idp = idp

  inv-l-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt (ap ! α) α) idp == idp [ _== idp ↓ !-inv-l p ]
  inv-l-lemma idp = idp

  inv-r-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α (ap ! α)) idp == idp [ _== idp ↓ !-inv-r p ]
  inv-r-lemma idp = idp

Trunc-⊙→Ω-group : ∀ {i j} (X : Ptd i) (Y : Ptd j) → Group (lmax i j)
Trunc-⊙→Ω-group X Y = Trunc-group (⊙→Ω-group-structure X Y)

{- [Trunc-→Ω-group] is functorial in the first argument -}

⊙→Ω-group-structure-fmap-dom : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  (f : X ⊙→ Y) (Z : Ptd k)
  → (⊙→Ω-group-structure Y Z →ᴳˢ ⊙→Ω-group-structure X Z)
⊙→Ω-group-structure-fmap-dom F Z = group-structure-hom (_⊙∘ F)
  (λ g₁ g₂ → ⊙∘-assoc ⊙Ω-∙ (⊙fanout g₁ g₂) F
           ∙ ap (⊙Ω-∙ ⊙∘_) (⊙fanout-pre∘ g₁ g₂ F))

Trunc-⊙→Ω-group-fmap-dom : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  (f : X ⊙→ Y) (Z : Ptd k)
  → (Trunc-⊙→Ω-group Y Z →ᴳ Trunc-⊙→Ω-group X Z)
Trunc-⊙→Ω-group-fmap-dom F Z =
  Trunc-group-fmap $ ⊙→Ω-group-structure-fmap-dom F Z

⊙→Ω-group-structure-emap-dom : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  (e : X ⊙≃ Y) (Z : Ptd k)
  → (⊙→Ω-group-structure Y Z ≃ᴳˢ ⊙→Ω-group-structure X Z)
⊙→Ω-group-structure-emap-dom (F , F-is-equiv) Z =
  ⊙→Ω-group-structure-fmap-dom F Z , pre⊙∘-is-equiv (F , F-is-equiv)

Trunc-⊙→Ω-group-emap-dom : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  (e : X ⊙≃ Y) (Z : Ptd k)
  → (Trunc-⊙→Ω-group Y Z ≃ᴳ Trunc-⊙→Ω-group X Z)
Trunc-⊙→Ω-group-emap-dom F Z =
  Trunc-group-emap $ ⊙→Ω-group-structure-emap-dom F Z

Trunc-⊙→Ω-group-fmap-dom-idf : ∀ {i j} {X : Ptd i} (Y : Ptd j)
  → Trunc-⊙→Ω-group-fmap-dom (⊙idf X) Y == idhom (Trunc-⊙→Ω-group X Y)
Trunc-⊙→Ω-group-fmap-dom-idf Y = group-hom= $ λ= $ Trunc-elim
  (λ _ → =-preserves-level _ Trunc-level) (λ _ → idp)

Trunc-⊙→Ω-group-fmap-dom-∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y) (W : Ptd l)
  → Trunc-⊙→Ω-group-fmap-dom (g ⊙∘ f) W
    == Trunc-⊙→Ω-group-fmap-dom f W ∘ᴳ Trunc-⊙→Ω-group-fmap-dom g W
Trunc-⊙→Ω-group-fmap-dom-∘ g f W = group-hom= $ λ= $
  Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
    (λ h → ap [_] (! (⊙∘-assoc h g f)))

⊙→Ω-group-structure-fmap-codom : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → Y ⊙→ Z → (⊙→Ω-group-structure X Y →ᴳˢ ⊙→Ω-group-structure X Z)
⊙→Ω-group-structure-fmap-codom X {Y} {Z} F = group-structure-hom
    (⊙Ω-fmap F ⊙∘_)
    (λ G H → ⊙λ= (λ x → Ω-fmap-∙ F ((fst G) x) ((fst H) x))
                 (lemma (snd F) (snd G) (snd H)))
    where
      abstract
        lemma : ∀ {ptZ : fst Z} (α : (fst F) (snd Y) == ptZ)
          {gpt hpt : Ω Y} (β : gpt == idp) (γ : hpt == idp)
          →  ⊙∘-pt (Ω-fmap (fst F , α)) (⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt β γ) idp) (snd (⊙Ω-fmap (fst F , α)))
          == ⊙∘-pt (fst ⊙Ω-∙)
               (⊙fanout-pt
                 (⊙∘-pt (Ω-fmap (fst F , α)) β (snd (⊙Ω-fmap (fst F , α))))
                 (⊙∘-pt (Ω-fmap (fst F , α)) γ (snd (⊙Ω-fmap (fst F , α))))
               ) idp
           [ _== idp ↓ Ω-fmap-∙ (fst F , α) gpt hpt ]
        lemma idp idp idp = idp

Trunc-⊙→Ω-group-fmap-codom : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → Y ⊙→ Z → Trunc-⊙→Ω-group X Y →ᴳ Trunc-⊙→Ω-group X Z
Trunc-⊙→Ω-group-fmap-codom X = Trunc-group-fmap ∘ ⊙→Ω-group-structure-fmap-codom X

⊙→Ω-group-structure-emap-codom : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → Y ⊙≃ Z → ⊙→Ω-group-structure X Y ≃ᴳˢ ⊙→Ω-group-structure X Z
⊙→Ω-group-structure-emap-codom X (F , F-is-equiv) =
  ⊙→Ω-group-structure-fmap-codom X F , post⊙∘-is-equiv (⊙Ω-emap (F , F-is-equiv))

Trunc-⊙→Ω-group-emap-codom : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → Y ⊙≃ Z → Trunc-⊙→Ω-group X Y ≃ᴳ Trunc-⊙→Ω-group X Z
Trunc-⊙→Ω-group-emap-codom X = Trunc-group-emap ∘ ⊙→Ω-group-structure-emap-codom X

-- TODO Check naming convensions.
-- TODO Use [CommSquareᴳ].
Trunc-⊙→Ω-group-fmap-nat : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (F : X₀ ⊙→ X₁) (G : Y₀ ⊙→ Y₁)
  →  Trunc-⊙→Ω-group-fmap-dom   F  Y₁ ∘ᴳ Trunc-⊙→Ω-group-fmap-codom X₁ G
  == Trunc-⊙→Ω-group-fmap-codom X₀ G  ∘ᴳ Trunc-⊙→Ω-group-fmap-dom   F  Y₀
Trunc-⊙→Ω-group-fmap-nat F G = group-hom= $ λ= $ Trunc-elim
  (λ _ → =-preserves-level _ Trunc-level)
  (λ k → ap [_] $ ⊙∘-assoc (⊙Ω-fmap G) k F)

{- Not used.
Trunc-⊙→Ω-group-emap-nat : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (F : X₀ ⊙≃ X₁) (G : Y₀ ⊙≃ Y₁)
  →  Trunc-⊙→Ω-group-emap-dom   F  Y₁ ∘ᴳ Trunc-⊙→Ω-group-emap-codom X₁ G
  == Trunc-⊙→Ω-group-emap-codom X₀ G  ∘ᴳ Trunc-⊙→Ω-group-emap-dom   F  Y₀
Trunc-⊙→Ω-group-emap-nat F G = group-hom=-to-iso= $ Trunc-⊙→Ω-group-fmap-nat F G
-}

-- XXX The following lemma about [⊙Bool→] does not really belong here.

{- Pointed maps out of bool -}

-- intuition : [f true] is fixed and the only changable part is [f false].

⊙Bool→-to-idf : ∀ {i} {X : Ptd i}
  → ⊙Bool ⊙→ X → fst X
⊙Bool→-to-idf (h , _) = h false

⊙Bool→-equiv-idf : ∀ {i} (X : Ptd i)
  → (⊙Bool ⊙→ X) ≃ fst X
⊙Bool→-equiv-idf {i} X = equiv ⊙Bool→-to-idf g f-g g-f
  where
  g : fst X → ⊙Bool ⊙→ X
  g x = (if_then snd X else x) , idp

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
      app= (λ= lemma) true ∙ hpt ∎)
    where lemma : ∀ b → fst (g (h false)) b == h b
          lemma true = ! hpt
          lemma false = idp

abstract
  Trunc-⊙Bool→Ω-iso-π₁ : ∀ {i} (X : Ptd i)
    → Trunc-⊙→Ω-group ⊙Bool X ≃ᴳ πS 0 X
  Trunc-⊙Bool→Ω-iso-π₁ {i} X = Trunc-group-emap (≃-to-≃ᴳˢ (⊙Bool→-equiv-idf (⊙Ω X)) (λ _ _ → idp))
