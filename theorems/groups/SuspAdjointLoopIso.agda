{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdAdjoint
open import groups.ToOmega

module groups.SuspAdjointLoopIso where

module SuspAdjointLoopIso {i} where

  import homotopy.SuspAdjointLoop {i} as A

  module _ (X Y : Ptd i) where

    abstract
      pres-comp : (h₁ h₂ : ⊙Susp X ⊙→ ⊙Ω Y)
        → –> (A.eq X (⊙Ω Y)) (⊙Ω-∙ ⊙∘ ⊙fanout h₁ h₂)
           == ⊙Ω-∙ ⊙∘ ⊙fanout (–> (A.eq X (⊙Ω Y)) h₁) (–> (A.eq X (⊙Ω Y)) h₂)
      pres-comp h₁ h₂ =
        B.nat-cod h₁ h₂ ⊙Ω-∙
        ∙ ap (_⊙∘ ⊙fanout (–> (A.eq X (⊙Ω Y)) h₁) (–> (A.eq X (⊙Ω Y)) h₂))
             arr2-lemma
        where
        module A× = RightAdjoint× A.hadj
        module B = RightAdjointBinary A.hadj

        ap2-lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
          (f : A × B → C) {r s : A × B} (p : r == s)
          → ap f p == ap2 (curry f) (ap fst p) (ap snd p)
        ap2-lemma f idp = idp

        ⊙ap2-lemma : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
          (f : X ⊙× Y ⊙→ Z)
          → ⊙Ω-fmap f == ⊙Ω-fmap2 f ⊙∘ ⊙fanout (⊙Ω-fmap ⊙fst) (⊙Ω-fmap ⊙snd)
        ⊙ap2-lemma (f , idp) = ⊙λ=' (ap2-lemma f) idp

        arr2-lemma : B.arr2 ⊙Ω-∙ == ⊙Ω-∙
        arr2-lemma =
          ⊙Ω-fmap ⊙Ω-∙ ⊙∘ A×.⊙out _ _
            =⟨ ⊙ap2-lemma ⊙Ω-∙ |in-ctx _⊙∘ A×.⊙out _ _ ⟩
          (⊙Ω-fmap2 ⊙Ω-∙ ⊙∘ A×.⊙into _ _) ⊙∘ A×.⊙out _ _
            =⟨ ⊙λ= $ ⊙∘-assoc (⊙Ω-fmap2 ⊙Ω-∙) (A×.⊙into _ _) (A×.⊙out _ _) ⟩
          ⊙Ω-fmap2 ⊙Ω-∙ ⊙∘ (A×.⊙into _ _ ⊙∘ A×.⊙out _ _)
            =⟨ A×.⊙into-out _ _ |in-ctx ⊙Ω-fmap2 ⊙Ω-∙ ⊙∘_ ⟩
          ⊙Ω-fmap2 ⊙Ω-∙
            =⟨ ⊙Ω-fmap2-∙ ⟩
          ⊙Ω-∙ ∎

    iso : Trunc-⊙→Ω-group (⊙Susp X) Y ≃ᴳ Trunc-⊙→Ω-group X (⊙Ω Y)
    iso = Trunc-group-emap (≃-to-≃ᴳˢ (A.eq X (⊙Ω Y)) pres-comp)

  abstract
    nat-dom : {X Y : Ptd i} (f : X ⊙→ Y) (Z : Ptd i)
      → fst (iso X Z) ∘ᴳ Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) Z
        == Trunc-⊙→Ω-group-fmap-dom f (⊙Ω Z) ∘ᴳ fst (iso Y Z)
    nat-dom f Z = group-hom= $ λ= $ Trunc-elim
      (λ g → ap [_] (! (A.nat-dom f (⊙Ω Z) g)))
