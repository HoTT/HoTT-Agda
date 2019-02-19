{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.EilenbergMacLane1 {i} (G : Group i) where
  private
    module G = Group G

    comp-equiv : ∀ g → G.El ≃ G.El
    comp-equiv g = equiv
      (λ x → G.comp x g)
      (λ x → G.comp x (G.inv g))
      (λ x → G.assoc x (G.inv g) g ∙ ap (G.comp x) (G.inv-l g) ∙ G.unit-r x)
      (λ x → G.assoc x g (G.inv g) ∙ ap (G.comp x) (G.inv-r g) ∙ G.unit-r x)

    comp-equiv-comp : (g₁ g₂ : G.El) → comp-equiv (G.comp g₁ g₂)
                      == (comp-equiv g₂ ∘e comp-equiv g₁)
    comp-equiv-comp g₁ g₂ =
      pair= (λ= (λ x → ! (G.assoc x g₁ g₂)))
            (prop-has-all-paths-↓ {B = is-equiv})

    Ω-group : Group (lsucc i)
    Ω-group = Ω^S-group 0
      ⊙[ (0 -Type i) , (G.El , G.El-level) ]

    Codes-hom : G →ᴳ Ω-group
    Codes-hom = group-hom (nType=-out ∘ ua ∘ comp-equiv) pres-comp where
      abstract
        pres-comp : ∀ g₁ g₂
          → nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv (G.comp g₁ g₂)))
          == nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₁))
          ∙ nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₂))
        pres-comp g₁ g₂ =
          nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv (G.comp g₁ g₂)))
            =⟨ comp-equiv-comp g₁ g₂ |in-ctx nType=-out ∘ ua ⟩
          nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₂ ∘e comp-equiv g₁))
            =⟨ ua-∘e (comp-equiv g₁) (comp-equiv g₂) |in-ctx nType=-out ⟩
          nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₁) ∙ ua (comp-equiv g₂))
            =⟨ ! $ nType-∙ {A = G.El , G.El-level} {B = G.El , G.El-level} {C = G.El , G.El-level}
                  (ua (comp-equiv g₁)) (ua (comp-equiv g₂)) ⟩
          nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₁))
          ∙ nType=-out {A = G.El , G.El-level} {B = G.El , G.El-level} (ua (comp-equiv g₂))
            =∎

    module CodesRec = EM₁Level₁Rec {G = G} {C = 0 -Type i} (G.El , G.El-level) Codes-hom

    Codes : EM₁ G → 0 -Type i
    Codes = CodesRec.f

    encode : {x : EM₁ G} → embase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α G.ident

    abstract
      transp-Codes-β : ∀ g g' → transport (fst ∘ Codes) (emloop g) g' == G.comp g' g
      transp-Codes-β g g' =
        coe (ap (fst ∘ Codes) (emloop g)) g'
          =⟨ ap (λ v → coe v g') (ap-∘ fst Codes (emloop g)) ⟩
        coe (ap fst (ap Codes (emloop g))) g'
          =⟨ ap (λ v → coe (ap fst v) g') (CodesRec.emloop-β g) ⟩
        coe (ap fst (nType=-out (ua (comp-equiv g)))) g'
          =⟨ ap (λ v → coe v g') (fst=-β (ua (comp-equiv g)) _) ⟩
        coe (ua (comp-equiv g)) g'
          =⟨ coe-β (comp-equiv g) g' ⟩
        –> (comp-equiv g) g' =∎

      encode-emloop : ∀ g → encode (emloop g) == g
      encode-emloop g =
        transport (fst ∘ Codes) (emloop g) G.ident
          =⟨ transp-Codes-β g G.ident ⟩
        G.comp G.ident g
          =⟨ G.unit-l g ⟩
        g =∎

    module Decode where

      private
        {- transport in path fibration of EM₁ -}
        transp-PF : embase' G == embase → embase' G == embase → embase' G == embase
        transp-PF = transport (embase' G ==_)

        {- transport in Codes -}
        transp-C : embase' G == embase → G.El → G.El
        transp-C = transport (fst ∘ Codes)

        transp-emloop : embase' G == embase → G.El → embase' G == embase
        transp-emloop p = transp-PF p ∘ emloop

        emloop-transp : embase' G == embase → G.El → embase' G == embase
        emloop-transp p = emloop ∘ transp-C p

        swap-transp-emloop-seq : ∀ g h → transp-emloop (emloop g) h =-= emloop-transp (emloop g) h
        swap-transp-emloop-seq g h =
          transp-emloop (emloop g) h
            =⟪ transp-cst=idf (emloop g) (emloop h) ⟫
          emloop h ∙ emloop g
            =⟪ ! (emloop-comp h g) ⟫
          emloop (G.comp h g)
            =⟪ ap emloop (! (transp-Codes-β g h)) ⟫
          emloop-transp (emloop g) h ∎∎

        swap-transp-emloop : ∀ g h → transp-emloop (emloop g) h == emloop-transp (emloop g) h
        swap-transp-emloop g h = ↯ (swap-transp-emloop-seq g h)

      private

        decode-emloop-comp : ∀ g₁ g₂ h →
          swap-transp-emloop (G.comp g₁ g₂) h ◃∙
          ap (λ p → emloop (transp-C p h)) (emloop-comp g₁ g₂) ◃∙
          ap emloop (transp-∙ (emloop g₁) (emloop g₂) h) ◃∎
          =ₛ
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop g₁ h) ◃∙
          swap-transp-emloop g₂ (transp-C (emloop g₁) h) ◃∎
        decode-emloop-comp g₁ g₂ h =
          swap-transp-emloop g₁g₂ h ◃∙
          ap (λ p → emloop-transp p h) (emloop-comp g₁ g₂) ◃∙
          ap emloop (transp-∙ (emloop g₁) (emloop g₂) h) ◃∎
            =ₛ₁⟨ 1 & 1 & ap-∘ emloop (λ p → transp-C p h) (emloop-comp g₁ g₂) ⟩
          swap-transp-emloop g₁g₂ h ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∙
          ap emloop (transp-∙ (emloop g₁) (emloop g₂) h) ◃∎
            =ₛ⟨ 0 & 1 & expand (swap-transp-emloop-seq g₁g₂ h) ⟩
          transp-cst=idf (emloop g₁g₂) (emloop h) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (transp-Codes-β g₁g₂ h)) ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∙
          ap emloop (transp-∙ (emloop g₁) (emloop g₂) h) ◃∎
            =ₛ⟨ 2 & 3 &
                ap-seq-=ₛ emloop $
                =ₛ-in {s = ! (transp-Codes-β g₁g₂ h) ◃∙
                           ap (λ p → transp-C p h) (emloop-comp g₁ g₂) ◃∙
                           transp-∙ (emloop g₁) (emloop g₂) h ◃∎}
                      {t = ! (G.assoc h g₁ g₂) ◃∙
                           ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h)) ◃∙
                           ! (transp-Codes-β g₂ (transp-C (emloop g₁) h)) ◃∎} $
                prop-path (has-level-apply G.El-level _ _) _ _
              ⟩
          transp-cst=idf (emloop g₁g₂) (emloop h) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (G.assoc h g₁ g₂)) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h))) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 0 & 1 &
                post-rotate-in {p = _ ◃∎} $ !ₛ $
                homotopy-naturality (λ p → transp-PF p (emloop h))
                                    (emloop h ∙_)
                                    (λ p → transp-cst=idf p (emloop h))
                                    (emloop-comp g₁ g₂)
              ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop h) ◃∙
          ! (ap (emloop h ∙_) (emloop-comp g₁ g₂)) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (G.assoc h g₁ g₂)) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h))) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ₁⟨ 4 & 1 & ap-! emloop (G.assoc h g₁ g₂) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop h) ◃∙
          ! (ap (emloop h ∙_) (emloop-comp g₁ g₂)) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ! (ap emloop (G.assoc h g₁ g₂)) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h))) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 2 & 3 & !ₛ (!-=ₛ (emloop-coh' G h g₁ g₂)) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop h) ◃∙
          ! (∙-assoc (emloop h) (emloop g₁) (emloop g₂)) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ! (emloop-comp (G.comp h g₁) g₂) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h))) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 1 & 2 &
                post-rotate'-in {p = _ ◃∙ _ ◃∙ _ ◃∎} $
                transp-cst=idf-pentagon (emloop g₁) (emloop g₂) (emloop h)
              ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ! (emloop-comp (G.comp h g₁) g₂) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h))) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ₁⟨ 6 & 1 & ∘-ap emloop (λ k → G.comp k g₂) (! (transp-Codes-β g₁ h)) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ! (emloop-comp (G.comp h g₁) g₂) ◃∙
          ap (λ k → emloop (G.comp k g₂)) (! (transp-Codes-β g₁ h)) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 5 & 2 & !ₛ $
                homotopy-naturality (λ k → emloop k ∙ emloop g₂)
                                    (λ k → emloop (G.comp k g₂))
                                    (λ k → ! (emloop-comp k g₂))
                                    (! (transp-Codes-β g₁ h))
              ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (transp-Codes-β g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ₁⟨ 4 & 1 & !-ap (_∙ emloop g₂) (emloop-comp h g₁) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ap (_∙ emloop g₂) (! (emloop-comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (transp-Codes-β g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 3 & 2 & !ₛ $
                homotopy-naturality (transp-PF (emloop g₂))
                                    (_∙ emloop g₂)
                                    (transp-cst=idf (emloop g₂))
                                    (! (emloop-comp h g₁))
              ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          transp-cst=idf (emloop g₂) (emloop (G.comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (transp-Codes-β g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ₁⟨ 5 & 1 & ap-∘ (_∙ emloop g₂) emloop (! (transp-Codes-β g₁ h)) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          transp-cst=idf (emloop g₂) (emloop (G.comp h g₁)) ◃∙
          ap (_∙ emloop g₂) (ap emloop (! (transp-Codes-β g₁ h))) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 4 & 2 & !ₛ $
                homotopy-naturality (transp-PF (emloop g₂))
                                    (_∙ emloop g₂)
                                    (transp-cst=idf (emloop g₂))
                                    (ap emloop (! (transp-Codes-β g₁ h)))
              ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          ap (transp-PF (emloop g₂)) (ap emloop (! (transp-Codes-β g₁ h))) ◃∙
          transp-cst=idf (emloop g₂) (emloop (transp-C (emloop g₁) h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 2 & 3 & ∙-ap-seq (transp-PF (emloop g₂)) (swap-transp-emloop-seq g₁ h) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop g₁ h) ◃∙
          transp-cst=idf (emloop g₂) (emloop (transp-C (emloop g₁) h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (transp-Codes-β g₂ (transp-C (emloop g₁) h))) ◃∎
            =ₛ⟨ 3 & 3 & contract ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop g₁ h) ◃∙
          swap-transp-emloop g₂ (transp-C (emloop g₁) h) ◃∎ ∎ₛ
          where g₁g₂ = G.comp g₁ g₂

      decode : {x : EM₁ G} → fst (Codes x) → embase == x
      decode {x} = Decode.f x
        where
        module Decode =
          EM₁Level₁FunElim {B = fst ∘ Codes} {C = embase' G ==_}
            emloop
            swap-transp-emloop
            decode-emloop-comp

    open Decode using (decode)

    decode-encode : ∀ {x} (α : embase' G == x) → decode (encode α) == α
    decode-encode idp = emloop-ident {G = G}

  emloop-equiv : G.El ≃ (embase' G == embase)
  emloop-equiv = equiv emloop encode decode-encode encode-emloop

  ⊙emloop-equiv : G.⊙El ⊙≃ ⊙Ω (⊙EM₁ G)
  ⊙emloop-equiv = ≃-to-⊙≃ emloop-equiv emloop-ident

  abstract
    instance
      EM₁-level₁ : {n : ℕ₋₂} → has-level (S (S (S n))) (EM₁ G)
      EM₁-level₁ {⟨-2⟩} = has-level-in pathspace-is-set
        where
        embase-loopspace-is-set : is-set (embase' G == embase)
        embase-loopspace-is-set = transport is-set (ua emloop-equiv) ⟨⟩
        pathspace-is-set : ∀ (x y : EM₁ G) → is-set (x == y)
        pathspace-is-set = EM₁-prop-elim (EM₁-prop-elim embase-loopspace-is-set)
      EM₁-level₁ {S n} = raise-level _ EM₁-level₁

  Ω¹-EM₁ : Ω^S-group 0 (⊙EM₁ G) ≃ᴳ G
  Ω¹-EM₁ = ≃-to-≃ᴳ (emloop-equiv ⁻¹)
    (λ l₁ l₂ → <– (ap-equiv emloop-equiv _ _) $
      emloop (encode (l₁ ∙ l₂))
        =⟨ decode-encode (l₁ ∙ l₂) ⟩
      l₁ ∙ l₂
        =⟨ ! $ ap2 _∙_ (decode-encode l₁) (decode-encode l₂) ⟩
      emloop (encode l₁) ∙ emloop (encode l₂)
        =⟨ ! $ emloop-comp (encode l₁) (encode l₂) ⟩
      emloop (G.comp (encode l₁) (encode l₂))
        =∎)

  π₁-EM₁ : πS 0 (⊙EM₁ G) ≃ᴳ G
  π₁-EM₁ = Ω¹-EM₁ ∘eᴳ unTrunc-iso (Ω^S-group-structure 0 (⊙EM₁ G))
