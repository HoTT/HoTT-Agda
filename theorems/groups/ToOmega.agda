{-# OPTIONS --without-K --rewriting #-}

open import HoTT

-- TODO Is it possible to have a more generic [→-group] construction?

module groups.ToOmega where

⊙→Ω-group-structure : ∀ {i j} (X : Ptd i) (Y : Ptd j)
  → GroupStructure (X ⊙→ ⊙Ω Y)
⊙→Ω-group-structure X Y = record {M} where
  module M where
    ident : (X ⊙→ ⊙Ω Y)
    ident = ⊙cst

    comp : (X ⊙→ ⊙Ω Y) → (X ⊙→ ⊙Ω Y) → (X ⊙→ ⊙Ω Y)
    comp F G = ⊙Ω-∙ ⊙∘ ⊙fanout F G

    inv : (X ⊙→ ⊙Ω Y) → (X ⊙→ ⊙Ω Y)
    inv F = (! ∘ fst F) , ap ! (snd F)
    abstract
      unit-l-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
        → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt {a₀ = idp} idp α) idp == α
      unit-l-lemma idp = idp

      unit-l : ∀ G → comp ident G == G
      unit-l G = ⊙λ=' (λ _ → idp) (unit-l-lemma (snd G))

      assoc-lemma : ∀ {i} {A : Type i} {x : A} {p q r : x == x}
        (α : p == idp) (β : q == idp) (γ : r == idp)
        →  ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt (⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α β) idp) γ) idp
        == ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt α (⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt β γ) idp)) idp
         [ _== idp ↓ ∙-assoc p q r ]
      assoc-lemma idp idp idp = idp

      assoc : ∀ F G H → comp (comp F G) H == comp F (comp G H)
      assoc F G H = ⊙λ='
        (λ x → ∙-assoc (fst F x) (fst G x) (fst H x))
        (assoc-lemma (snd F) (snd G) (snd H))

      inv-l-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
        → ⊙∘-pt (fst ⊙Ω-∙) (⊙fanout-pt (ap ! α) α) idp == idp [ _== idp ↓ !-inv-l p ]
      inv-l-lemma idp = idp

      inv-l : ∀ F → comp (inv F) F == ident
      inv-l F = ⊙λ=' (!-inv-l ∘ fst F) (inv-l-lemma (snd F))

Trunc-⊙→Ω-group : ∀ {i j} (X : Ptd i) (Y : Ptd j) → Group (lmax i j)
Trunc-⊙→Ω-group X Y = Trunc-group (⊙→Ω-group-structure X Y)

{- [Trunc-→Ω-group] is contravariantly functorial in the first argument -}

⊙→Ω-group-structure-fmap-dom : ∀ {i j k} {X : Ptd i} {Y : Ptd j}
  (f : X ⊙→ Y) (Z : Ptd k)
  → (⊙→Ω-group-structure Y Z →ᴳˢ ⊙→Ω-group-structure X Z)
⊙→Ω-group-structure-fmap-dom F Z = group-structure-hom (_⊙∘ F)
  (λ g₁ g₂ → ⊙λ= (⊙∘-assoc ⊙Ω-∙ (⊙fanout g₁ g₂) F)
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
Trunc-⊙→Ω-group-fmap-dom-idf Y = group-hom= $ λ= $ Trunc-elim (λ _ → idp)

Trunc-⊙→Ω-group-fmap-dom-∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y) (W : Ptd l)
  → Trunc-⊙→Ω-group-fmap-dom (g ⊙∘ f) W
    == Trunc-⊙→Ω-group-fmap-dom f W ∘ᴳ Trunc-⊙→Ω-group-fmap-dom g W
Trunc-⊙→Ω-group-fmap-dom-∘ g f W = group-hom= $ λ= $
  Trunc-elim (λ h → ap [_] (! (⊙λ= $ ⊙∘-assoc h g f)))

{- [Trunc-→Ω-group] is covariantly functorial in the second argument -}

⊙→Ω-group-structure-fmap-codom : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k}
  → Y ⊙→ Z → (⊙→Ω-group-structure X Y →ᴳˢ ⊙→Ω-group-structure X Z)
⊙→Ω-group-structure-fmap-codom X {Y} {Z} F = group-structure-hom
    (⊙Ω-fmap F ⊙∘_)
    (λ G H → ⊙λ=' (λ x → Ω-fmap-∙ F ((fst G) x) ((fst H) x))
                  (lemma (snd F) (snd G) (snd H)))
    where
      abstract
        lemma : ∀ {ptZ : de⊙ Z} (α : (fst F) (pt Y) == ptZ)
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

Trunc-⊙→Ω-group-fmap-codom-idf : ∀ {i j} (X : Ptd i) (Y : Ptd j)
  → Trunc-⊙→Ω-group-fmap-codom X (⊙idf Y) == idhom (Trunc-⊙→Ω-group X Y)
Trunc-⊙→Ω-group-fmap-codom-idf X Y = group-hom= $ λ= $
  Trunc-elim (λ h → ap [_]₀ (ap (_⊙∘ h) ⊙Ω-fmap-idf ∙ ⊙λ= (⊙∘-unit-l h)))

Trunc-⊙→Ω-group-fmap-codom-∘ : ∀ {i j k l} (W : Ptd i)
  {X : Ptd j} {Y : Ptd k} {Z : Ptd l}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → Trunc-⊙→Ω-group-fmap-codom W (g ⊙∘ f) ==
    Trunc-⊙→Ω-group-fmap-codom W g ∘ᴳ Trunc-⊙→Ω-group-fmap-codom W f
Trunc-⊙→Ω-group-fmap-codom-∘ W g f = group-hom= $ λ= $
  Trunc-elim $ λ h →
  ap [_]₀ (ap (_⊙∘ h) (⊙Ω-fmap-∘ g f) ∙ ⊙λ= (⊙∘-assoc (⊙Ω-fmap g) (⊙Ω-fmap f) h))

-- TODO Check naming convensions.
-- TODO Use [CommSquareᴳ].
Trunc-⊙→Ω-group-fmap-nat : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (F : X₀ ⊙→ X₁) (G : Y₀ ⊙→ Y₁)
  →  Trunc-⊙→Ω-group-fmap-dom   F  Y₁ ∘ᴳ Trunc-⊙→Ω-group-fmap-codom X₁ G
  == Trunc-⊙→Ω-group-fmap-codom X₀ G  ∘ᴳ Trunc-⊙→Ω-group-fmap-dom   F  Y₀
Trunc-⊙→Ω-group-fmap-nat F G = group-hom= $ λ= $ Trunc-elim
  (λ k → ap [_] $ ⊙λ= $ ⊙∘-assoc (⊙Ω-fmap G) k F)

{- Not used.
Trunc-⊙→Ω-group-emap-nat : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (F : X₀ ⊙≃ X₁) (G : Y₀ ⊙≃ Y₁)
  →  Trunc-⊙→Ω-group-emap-dom   F  Y₁ ∘ᴳ Trunc-⊙→Ω-group-emap-codom X₁ G
  == Trunc-⊙→Ω-group-emap-codom X₀ G  ∘ᴳ Trunc-⊙→Ω-group-emap-dom   F  Y₀
Trunc-⊙→Ω-group-emap-nat F G = group-hom=-to-iso= $ Trunc-⊙→Ω-group-fmap-nat F G
-}

{- Pointed maps out of bool -}

Trunc-⊙Bool→Ω-iso-π₁ : ∀ {i} (X : Ptd i)
  → Trunc-⊙→Ω-group ⊙Bool X ≃ᴳ πS 0 X
Trunc-⊙Bool→Ω-iso-π₁ {i} X = Trunc-group-emap (≃-to-≃ᴳˢ (⊙Bool→-equiv-idf (⊙Ω X)) (λ _ _ → idp))
