{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdAdjoint
open import groups.FromSusp
open import groups.ToOmega

module groups.SuspAdjointLoopIso {i} where

  import homotopy.SuspAdjointLoop {i} as A

  module _ (X Y : Ptd i) where

    private
      pres-comp : preserves-comp
        (GroupStructure.comp (⊙→Ω-group-structure (⊙Susp X) Y))
        (GroupStructure.comp (⊙→Ω-group-structure X (⊙Ω Y)))
        (–> (A.eq X (⊙Ω Y)))
    abstract
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

    ⊙→Ω-iso-⊙→Ω : ⊙→Ω-group-structure (⊙Susp X) Y ≃ᴳˢ ⊙→Ω-group-structure X (⊙Ω Y)
    ⊙→Ω-iso-⊙→Ω = ≃-to-≃ᴳˢ (A.eq X (⊙Ω Y)) pres-comp

    Trunc-⊙→Ω-iso-Trunc-⊙→Ω : Trunc-⊙→Ω-group (⊙Susp X) Y ≃ᴳ Trunc-⊙→Ω-group X (⊙Ω Y)
    Trunc-⊙→Ω-iso-Trunc-⊙→Ω = Trunc-group-emap ⊙→Ω-iso-⊙→Ω

  abstract
    Trunc-⊙→Ω-iso-Trunc-⊙→Ω-nat-dom : {X Y : Ptd i} (f : X ⊙→ Y) (Z : Ptd i)
      → fst (Trunc-⊙→Ω-iso-Trunc-⊙→Ω X Z) ∘ᴳ Trunc-⊙→Ω-group-fmap-dom (⊙Susp-fmap f) Z
        == Trunc-⊙→Ω-group-fmap-dom f (⊙Ω Z) ∘ᴳ fst (Trunc-⊙→Ω-iso-Trunc-⊙→Ω Y Z)
    Trunc-⊙→Ω-iso-Trunc-⊙→Ω-nat-dom f Z = group-hom= $ λ= $ Trunc-elim
      (λ g → ap [_] (! (A.nat-dom f (⊙Ω Z) g)))

  module _ (X Y : Ptd i) where

    private
      pres-comp'' : ∀ h₀ h₁ →
          fst (<– (A.eq X Y) (GroupStructure.comp (⊙→Ω-group-structure X Y) (–> (A.eq X Y) h₀) (–> (A.eq X Y) h₁)))
        ∼ fst (GroupStructure.comp (Susp⊙→-group-structure X Y) h₀ h₁)
      pres-comp'' (h₀ , idp) (h₁ , h₁-pt) =
        Susp-elim
          idp
          (! h₁-pt ∙ ap h₁ (merid (pt X)))
          (λ x → ↓-='-in' $
            ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt)) ∘ pinch X) (merid x)
              =⟨ ap-∘ (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (pinch X) (merid x)  ⟩
            ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (ap (pinch X) (merid x))
              =⟨ ap (ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt)))) (Pinch.merid-β X x) ⟩
            ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (ap winl (σloop X x) ∙ wglue ∙ ap winr (merid x))
              =⟨ ap-∙∙ (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (ap winl (σloop X x)) wglue (ap winr (merid x)) ⟩
            ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (ap winl (σloop X x))
            ∙ ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) wglue
            ∙ ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) (ap winr (merid x))
              =⟨ ap3 (λ p q r → p ∙ q ∙ r)
                   (∘-ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) winl (σloop X x))
                   (⊙WedgeRec.glue-β (h₀ , idp) (h₁ , h₁-pt))
                   (∘-ap (fst (⊙Wedge-rec (h₀ , idp) (h₁ , h₁-pt))) winr (merid x)) ⟩
            ap h₀ (σloop X x) ∙ ! h₁-pt ∙ ap h₁ (merid x)
              =⟨ lemma h₁ (ap h₀ (σloop X x)) h₁-pt (merid x) (merid (pt X)) h₁-pt ⟩
            (ap h₀ (σloop X x) ∙ (! h₁-pt ∙ ap h₁ (σloop X x) ∙' h₁-pt)) ∙' (! h₁-pt ∙ ap h₁ (merid (pt X)))
              =⟨ ap (λ p → p ∙' (! h₁-pt ∙ ap h₁ (merid (pt X)))) $
                  ap h₀ (σloop X x) ∙ (! h₁-pt ∙ ap h₁ (σloop X x) ∙' h₁-pt)
                    =⟨ ! $ ap (ap h₀ (σloop X x) ∙_) (Ω-fmap-β (h₁ , h₁-pt) (σloop X x)) ⟩
                  ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x)
                    =⟨ ! $ A.Eta.merid-β Y (ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x)) ⟩
                  ap (fst (A.ε Y)) (merid (ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x)))
                    =⟨ ! $ ap (ap (fst (A.ε Y))) (SuspFmap.merid-β (λ x → ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x)) x) ⟩
                  ap (fst (A.ε Y)) (ap (Susp-fmap (λ x → ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x))) (merid x))
                    =⟨ ∘-ap (fst (A.ε Y)) (Susp-fmap (λ x → ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x))) (merid x) ⟩
                  ap (fst (A.ε Y) ∘ Susp-fmap (λ x → ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x))) (merid x)
                    =∎ ⟩
            ap (fst (A.ε Y) ∘ Susp-fmap (λ x → ap h₀ (σloop X x) ∙ Ω-fmap (h₁ , h₁-pt) (σloop X x))) (merid x)
            ∙' (! h₁-pt ∙ ap h₁ (merid (pt X)))
              =∎)
        where
        lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
          {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B} (p₀ : b₀ == b₁) (p₁ : f a₀ == b₁)
          (p₂ : a₀ == a₁) (p₃ : a₂ == a₁) (p₄ : f a₂ == b₂)
          → p₀ ∙ ! p₁ ∙ ap f p₂ == (p₀ ∙ (! p₁ ∙ ap f (p₂ ∙ ! p₃) ∙' p₄)) ∙' (! p₄ ∙ ap f p₃)
        lemma f idp idp idp idp idp = idp

      pres-comp' : ∀ h₀ h₁ →
           <– (A.eq X Y) (GroupStructure.comp (⊙→Ω-group-structure X Y) (–> (A.eq X Y) h₀) (–> (A.eq X Y) h₁))
        ⊙∼ GroupStructure.comp (Susp⊙→-group-structure X Y) h₀ h₁
      pres-comp' (h₀ , idp) (h₁ , h₁-pt) =
        pres-comp'' (h₀ , idp) (h₁ , h₁-pt) , idp

      pres-comp : preserves-comp
        (GroupStructure.comp (Susp⊙→-group-structure X Y))
        (GroupStructure.comp (⊙→Ω-group-structure X Y))
        (–> (A.eq X Y))
      pres-comp h₀ h₁ =
        –> (A.eq X Y) (GroupStructure.comp (Susp⊙→-group-structure X Y) h₀ h₁)
          =⟨ ! (ap (–> (A.eq X Y)) (⊙λ= (pres-comp' h₀ h₁))) ⟩
        –> (A.eq X Y) (<– (A.eq X Y) (GroupStructure.comp (⊙→Ω-group-structure X Y) (–> (A.eq X Y) h₀) (–> (A.eq X Y) h₁)))
          =⟨ <–-inv-r (A.eq X Y) (GroupStructure.comp (⊙→Ω-group-structure X Y) (–> (A.eq X Y) h₀) (–> (A.eq X Y) h₁)) ⟩
        GroupStructure.comp (⊙→Ω-group-structure X Y) (–> (A.eq X Y) h₀) (–> (A.eq X Y) h₁)
          =∎

    Susp⊙→-iso-⊙→Ω : Susp⊙→-group-structure X Y ≃ᴳˢ ⊙→Ω-group-structure X Y
    Susp⊙→-iso-⊙→Ω = ≃-to-≃ᴳˢ (A.eq X Y) pres-comp
