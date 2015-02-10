{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.KGn

module cohomology.WithCoefficients where

→Ω-group-structure : ∀ {i j} (X : Ptd i) (Y : Ptd j)
  → GroupStructure (fst (X ⊙→ ⊙Ω Y))
→Ω-group-structure X Y = record {
  ident = ((λ _ → idp) , idp);
  inv = λ F → ((! ∘ fst F) , ap ! (snd F));
  comp = λ F G →
    ((λ x → fst F x ∙ fst G x), ap2 _∙_ (snd F) (snd G));
  unitl = λ G → pair= idp (ap2-idp-l _∙_ {x = idp} (snd G) ∙ ap-idf (snd G));
  unitr = λ F → pair=
    (λ= (∙-unit-r ∘ fst F))
    (↓-app=cst-in $
      ap2 _∙_ (snd F) idp
        =⟨ ap2-idp-r _∙_ (snd F) ⟩
      ap (λ p → p ∙ idp) (snd F)
        =⟨ unitr-lemma (snd F) ⟩
      ∙-unit-r (fst F (snd X)) ∙ snd F
        =⟨ ap (λ w → w ∙ snd F) (! (app=-β (∙-unit-r ∘ fst F) (snd X))) ⟩
      app= (λ= (∙-unit-r ∘ fst F)) (snd X) ∙ snd F
      ∎);
  assoc = λ F G H → pair=
    (λ= (λ x → ∙-assoc (fst F x) (fst G x) (fst H x)))
    (↓-app=cst-in $
      ap2 _∙_ (ap2 _∙_ (snd F) (snd G)) (snd H)
        =⟨ ! (∙-unit-r _) ∙ assoc-lemma (snd F) (snd G) (snd H) ⟩
      ∙-assoc (fst F (snd X)) (fst G (snd X)) (fst H (snd X))
       ∙ ap2 _∙_ (snd F) (ap2 _∙_ (snd G) (snd H))
        =⟨ ! (app=-β (λ x → ∙-assoc (fst F x) (fst G x) (fst H x)) (snd X))
           |in-ctx (λ w → w ∙ ap2 _∙_ (snd F) (ap2 _∙_ (snd G) (snd H))) ⟩
      app= (λ= (λ x → ∙-assoc (fst F x) (fst G x) (fst H x))) (snd X)
       ∙ ap2 _∙_ (snd F) (ap2 _∙_ (snd G) (snd H))
      ∎);
  invl = λ F → pair=
    (λ= (!-inv-l ∘ fst F))
    (↓-app=cst-in $
     ap2 _∙_ (ap ! (snd F)) (snd F)
        =⟨ invl-lemma (snd F) ⟩
      !-inv-l (fst F (snd X))
        =⟨ ! (app=-β (!-inv-l ∘ fst F) (snd X)) ⟩
      app= (λ= (!-inv-l ∘ fst F)) (snd X)
        =⟨ ! (∙-unit-r _) ⟩
      app= (λ= (!-inv-l ∘ fst F)) (snd X) ∙ idp
      ∎);
  invr = λ F → pair=
    (λ= (!-inv-r ∘ fst F))
    (↓-app=cst-in $
      ap2 _∙_ (snd F) (ap ! (snd F))
        =⟨ invr-lemma (snd F) ⟩
      !-inv-r (fst F (snd X))
        =⟨ ! (app=-β (!-inv-r ∘ fst F) (snd X)) ⟩
      app= (λ= (!-inv-r ∘ fst F)) (snd X)
        =⟨ ! (∙-unit-r _) ⟩
      app= (λ= (!-inv-r ∘ fst F)) (snd X) ∙ idp
      ∎)}
  where

  unitr-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ap (λ r → r ∙ idp) α == ∙-unit-r p ∙ α
  unitr-lemma idp = idp

  assoc-lemma : ∀ {i} {A : Type i} {w x y z : A}
    {p₁ p₂ : w == x} {q₁ q₂ : x == y} {r₁ r₂ : y == z}
    (α : p₁ == p₂) (β : q₁ == q₂) (γ : r₁ == r₂)
    → ap2 _∙_ (ap2 _∙_ α β) γ ∙ ∙-assoc p₂ q₂ r₂ ==
      ∙-assoc p₁ q₁ r₁ ∙ ap2 _∙_ α (ap2 _∙_ β γ)
  assoc-lemma idp idp idp = ! (∙-unit-r _)

  invl-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ap2 _∙_ (ap ! α) α == !-inv-l p
  invl-lemma idp = idp

  invr-lemma : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
    → ap2 _∙_ α (ap ! α) == !-inv-r p
  invr-lemma idp = idp

→Ω-Group : ∀ {i j} (X : Ptd i) (Y : Ptd j) → Group (lmax i j)
→Ω-Group X Y = Trunc-Group (→Ω-group-structure X Y)

{- Some lemmas to be used to calculate cohomology of S⁰ -}
Bool⊙→-out : ∀ {i} {X : Ptd i}
  → fst (⊙Lift {j = i} ⊙Bool ⊙→ X) → fst X
Bool⊙→-out (h , _) = h (lift false)

Bool⊙→-equiv : ∀ {i} (X : Ptd i)
  → fst (⊙Lift {j = i} ⊙Bool ⊙→ X) ≃ fst X
Bool⊙→-equiv {i} X = equiv Bool⊙→-out g f-g g-f
  where
  g : fst X → fst (⊙Lift {j = i} ⊙Bool ⊙→ X)
  g x = ((λ {(lift b) → if b then snd X else x}) , idp)

  f-g : ∀ x → Bool⊙→-out (g x) == x
  f-g x = idp

  g-f : ∀ H → g (Bool⊙→-out H) == H
  g-f (h , hpt) = pair=
    (λ= lemma)
    (↓-app=cst-in $
      idp
        =⟨ ! (!-inv-l hpt) ⟩
      ! hpt ∙ hpt
        =⟨ ! (app=-β lemma (lift true)) |in-ctx (λ w → w ∙ hpt) ⟩
      app= (λ= lemma) (lift true) ∙ hpt ∎)
    where lemma : ∀ b → fst (g (h (lift false))) b == h b
          lemma (lift true) = ! hpt
          lemma (lift false) = idp

abstract
  Bool⊙→-path : ∀ {i} (X : Ptd i)
    → fst (⊙Lift {j = i} ⊙Bool ⊙→ X) == fst X
  Bool⊙→-path X = ua (Bool⊙→-equiv X)

abstract
  Bool⊙→Ω-iso-π₁ : ∀ {i} (X : Ptd i)
    → →Ω-Group (⊙Lift {j = i} ⊙Bool) X == π 1 (ℕ-S≠O _) X
  Bool⊙→Ω-iso-π₁ {i} X =
    group-iso
      (record {
        f = Trunc-fmap Bool⊙→-out;
        pres-comp = Trunc-elim {i = i}
          (λ _ → Π-level {j = i} (λ _ → =-preserves-level _ Trunc-level))
          (λ g₁ → Trunc-elim
            (λ _ → =-preserves-level _ Trunc-level)
            (λ g₂ → idp))})
      (is-equiv-Trunc ⟨0⟩ _ (snd (Bool⊙→-equiv (⊙Ω X))))

Bool⊙→KG0-iso-G : ∀ {i} (G : Group i) (abel : is-abelian G)
  → →Ω-Group (⊙Lift {j = i} ⊙Bool) (KGnExplicit.⊙KG G abel 1) == G
Bool⊙→KG0-iso-G G abel =
  Bool⊙→Ω-iso-π₁ (KGnExplicit.⊙KG G abel 1)
  ∙ KGnExplicit.π-diag G abel 1 (ℕ-S≠O _)
