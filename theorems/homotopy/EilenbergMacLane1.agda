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

    comp-equiv-id : comp-equiv G.ident == ide G.El
    comp-equiv-id =
      pair= (λ= G.unit-r)
            (prop-has-all-paths-↓ {B = is-equiv})

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

    abstract
      ↓-Codes-loop : ∀ g g' → g' == G.comp g' g [ fst ∘ Codes ↓ emloop g ]
      ↓-Codes-loop g g' =
        ↓-ap-out fst Codes (emloop g) $
        ↓-ap-out (idf _) fst (ap Codes (emloop g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ ap fst w ])
                  (! (CodesRec.emloop-β g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ w ])
                  (! (fst=-β (ua $ comp-equiv g) _)) $
        ↓-idf-ua-in (comp-equiv g) idp

    ↓-Codes-loop-transp : ∀ g g' → transport (fst ∘ Codes) (emloop g) g' == G.comp g' g
    ↓-Codes-loop-transp g g' = to-transp (↓-Codes-loop g g')

    encode : {x : EM₁ G} → embase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α G.ident

    encode-emloop : ∀ g → encode (emloop g) == g
    encode-emloop g = to-transp $
      transport (λ x → G.ident == x [ fst ∘ Codes ↓ emloop g ])
                (G.unit-l g) (↓-Codes-loop g G.ident)

    module Decode where

      P : EM₁ G → Type i
      P x' = fst (Codes x') → embase == x'

      Q : embase' G == embase → Type i
      Q p = emloop == emloop [ P ↓ p ]

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

      module _ (g : G.El) where
        module _ (h : G.El) where
          swap-transp-emloop'-seq : transp-emloop (emloop g) h =-= emloop-transp (emloop g) h
          swap-transp-emloop'-seq =
            transp-cst=idf (emloop g) (emloop h) ◃∙
            ! (emloop-comp h g) ◃∙
            ap emloop (! (↓-Codes-loop-transp g h)) ◃∎

          swap-transp-emloop' : transp-emloop (emloop g) h == emloop-transp (emloop g) h
          swap-transp-emloop' = ↯ swap-transp-emloop'-seq

        swap-transp-emloop : transp-emloop (emloop g) == emloop-transp (emloop g)
        swap-transp-emloop = λ= swap-transp-emloop'

        loop' : Q (emloop g)
        loop' = ↓-→-from-transp swap-transp-emloop

      module _ (g₁ g₂ : G.El) where

        g₁g₂ : G.El
        g₁g₂ = G.comp g₁ g₂

        swap-transp-emloop-2 : transp-emloop (emloop g₁ ∙ emloop g₂) ∼
                               emloop-transp (emloop g₁ ∙ emloop g₂)
        swap-transp-emloop-2 =
          comp-transp {B = fst ∘ Codes} {C = embase ==_}
                      {u = emloop} {u' = emloop} {u'' = emloop}
                      (emloop g₁) (emloop g₂)
                      (swap-transp-emloop g₁) (swap-transp-emloop g₂)

        DD : ∀ h →
          app= (swap-transp-emloop g₁g₂) h ◃∙
          app= (ap emloop-transp (emloop-comp g₁ g₂)) h ◃∎
          =ₛ
          app= (ap transp-emloop (emloop-comp g₁ g₂)) h ◃∙
          app= (λ= swap-transp-emloop-2) h ◃∎
        DD h =
          app= (swap-transp-emloop g₁g₂) h ◃∙
          app= (ap emloop-transp (emloop-comp g₁ g₂)) h ◃∎
            =ₛ₁⟨ 0 & 1 & app=-β (swap-transp-emloop' g₁g₂) h ⟩
          swap-transp-emloop' g₁g₂ h ◃∙
          app= (ap emloop-transp (emloop-comp g₁ g₂)) h ◃∎
            =ₛ₁⟨ 1 & 1 & ∘-ap (λ k → k h) emloop-transp (emloop-comp g₁ g₂) ⟩
          swap-transp-emloop' g₁g₂ h ◃∙
          ap (λ p → emloop-transp p h) (emloop-comp g₁ g₂) ◃∎
            =ₛ₁⟨ 1 & 1 & ap-∘ emloop (λ p → transp-C p h) (emloop-comp g₁ g₂) ⟩
          swap-transp-emloop' g₁g₂ h ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∎
            =ₛ⟨ 0 & 1 & expand (swap-transp-emloop'-seq g₁g₂ h) ⟩
          transp-cst=idf (emloop g₁g₂) (emloop h) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₁g₂ h)) ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∎
            =ₛ⟨ 0 & 1 &
                post-rotate-in {p = _ ◃∎} $ !ₛ $
                homotopy-naturality (λ p → transp-PF p (emloop h))
                                    (emloop h ∙_)
                                    (λ p → transp-cst=idf p (emloop h))
                                    (emloop-comp g₁ g₂) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop h) ◃∙
          ! (ap (emloop h ∙_) (emloop-comp g₁ g₂)) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₁g₂ h)) ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∎
            =ₛ⟨ 1 & 1 & transp-cst=idf-pentagon (emloop g₁) (emloop g₂) (emloop h) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ∙-assoc (emloop h) (emloop g₁) (emloop g₂) ◃∙
          ! (ap (emloop h ∙_) (emloop-comp g₁ g₂)) ◃∙
          ! (emloop-comp h g₁g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₁g₂ h)) ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∎
            =ₛ⟨ 4 & 3 &
                post-rotate'-seq-in {p = _ ◃∙ _ ◃∙ _ ◃∎} $
                pre-rotate-seq-in {p = _ ◃∙ _ ◃∎} $
                emloop-coh' G h g₁ g₂ ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (λ l → l ∙ emloop' G g₂) (emloop-comp' G h g₁)) ◃∙
          ! (emloop-comp' G (G.comp h g₁) g₂) ◃∙
          ap emloop (G.assoc h g₁ g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₁g₂ h)) ◃∙
          ap emloop (ap (λ p → transp-C p h) (emloop-comp g₁ g₂)) ◃∎
            =ₛ⟨ 6 & 3 &
                ap-seq-=ₛ emloop $
                =ₛ-in {s = G.assoc h g₁ g₂ ◃∙
                           ! (↓-Codes-loop-transp g₁g₂ h) ◃∙
                           ap (λ p → transp-C p h) (emloop-comp g₁ g₂) ◃∎}
                      {t = ap (λ k → G.comp k g₂) (! (↓-Codes-loop-transp g₁ h)) ◃∙
                           ! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h)) ◃∙
                           ! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h) ◃∎} $
                prop-path (has-level-apply G.El-level _ _) _ _
              ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp' G h g₁)) ◃∙
          ! (emloop-comp (G.comp h g₁) g₂) ◃∙
          ap emloop (ap (λ k → G.comp k g₂) (! (↓-Codes-loop-transp g₁ h))) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 6 & 1 & ∘-ap emloop (λ k → G.comp k g₂) (! (↓-Codes-loop-transp g₁ h)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ! (emloop-comp (G.comp h g₁) g₂) ◃∙
          ap (λ k → emloop (G.comp k g₂)) (! (↓-Codes-loop-transp g₁ h)) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 5 & 2 & !ₛ $
                homotopy-naturality (λ k → emloop k ∙ emloop g₂)
                                    (λ k → emloop (G.comp k g₂))
                                    (λ k → ! (emloop-comp k g₂))
                                    (! (↓-Codes-loop-transp g₁ h)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ! (ap (_∙ emloop g₂) (emloop-comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (↓-Codes-loop-transp g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 4 & 1 & !-ap (_∙ emloop g₂) (emloop-comp h g₁) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          transp-cst=idf (emloop g₂) (emloop h ∙ emloop g₁) ◃∙
          ap (_∙ emloop g₂) (! (emloop-comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (↓-Codes-loop-transp g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 3 & 2 & !ₛ $
                homotopy-naturality (transp-PF (emloop g₂))
                                    (_∙ emloop g₂)
                                    (transp-cst=idf (emloop g₂))
                                    (! (emloop-comp h g₁)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          transp-cst=idf (emloop g₂) (emloop (G.comp h g₁)) ◃∙
          ap (λ k → emloop k ∙ emloop g₂) (! (↓-Codes-loop-transp g₁ h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 5 & 1 & ap-∘ (_∙ emloop g₂) emloop (! (↓-Codes-loop-transp g₁ h)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          transp-cst=idf (emloop g₂) (emloop (G.comp h g₁)) ◃∙
          ap (_∙ emloop g₂) (ap emloop (! (↓-Codes-loop-transp g₁ h))) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 4 & 2 & !ₛ $
                homotopy-naturality (transp-PF (emloop g₂))
                                    (_∙ emloop g₂)
                                    (transp-cst=idf (emloop g₂))
                                    (ap emloop (! (↓-Codes-loop-transp g₁ h))) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (transp-cst=idf (emloop g₁) (emloop h)) ◃∙
          ap (transp-PF (emloop g₂)) (! (emloop-comp h g₁)) ◃∙
          ap (transp-PF (emloop g₂)) (ap emloop (! (↓-Codes-loop-transp g₁ h))) ◃∙
          transp-cst=idf (emloop g₂) (emloop (transp-C (emloop g₁) h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 2 & 3 & ∙-ap-seq (transp-PF (emloop g₂)) (swap-transp-emloop'-seq g₁ h) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop' g₁ h) ◃∙
          transp-cst=idf (emloop g₂) (emloop (transp-C (emloop g₁) h)) ◃∙
          ! (emloop-comp (transp-C (emloop g₁) h) g₂) ◃∙
          ap emloop (! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) h))) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 3 & 3 & contract ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop' g₁ h) ◃∙
          swap-transp-emloop' g₂ (transp-C (emloop g₁) h) ◃∙
          ap emloop (! (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 4 & 1 & ap-! emloop (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (swap-transp-emloop' g₁ h) ◃∙
          swap-transp-emloop' g₂ (transp-C (emloop g₁) h) ◃∙
          ! (ap emloop (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 2 & 1 & ap (ap (transp-PF (emloop g₂)))
                            (! (app=-β (swap-transp-emloop' g₁) h)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (app= (swap-transp-emloop g₁) h) ◃∙
          swap-transp-emloop' g₂ (transp-C (emloop g₁) h) ◃∙
          ! (ap emloop (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ₁⟨ 3 & 1 & ! (app=-β (swap-transp-emloop' g₂) (transp-C (emloop g₁) h)) ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (emloop h) ◃∙
          ap (transp-PF (emloop g₂)) (app= (swap-transp-emloop g₁) h) ◃∙
          app= (swap-transp-emloop g₂) (transp-C (emloop g₁) h) ◃∙
          ! (ap emloop (transp-∙ {B = fst ∘ Codes} (emloop g₁) (emloop g₂) h)) ◃∎
            =ₛ⟨ 1 & 4 & contract ⟩
          ap (λ p → transp-PF p (emloop h)) (emloop-comp g₁ g₂) ◃∙
          swap-transp-emloop-2 h ◃∎
            =ₛ₁⟨ 1 & 1 & ! (app=-β swap-transp-emloop-2 h) ⟩
          ap (λ p → transp-emloop p h) (emloop-comp g₁ g₂) ◃∙
          app= (λ= swap-transp-emloop-2) h ◃∎
            =ₛ₁⟨ 0 & 1 & ap-∘ (λ k → k h) transp-emloop (emloop-comp g₁ g₂) ⟩
          app= (ap transp-emloop (emloop-comp g₁ g₂)) h ◃∙
          app= (λ= swap-transp-emloop-2) h ◃∎ ∎ₛ

        EE : swap-transp-emloop g₁g₂ ∙ ap emloop-transp (emloop-comp g₁ g₂) ==
             ap transp-emloop (emloop-comp g₁ g₂) ∙ λ= swap-transp-emloop-2
        EE =
          –>-is-inj (app=-equiv {A = G.El} {P = λ _ → embase' G == embase}
                                {f = transp-emloop (emloop g₁g₂)}
                                {g = emloop-transp (emloop g₁ ∙ emloop g₂)})
                    _ _ $
          λ= {A = G.El} {P = λ x → transp-emloop (emloop g₁g₂) x == emloop-transp (emloop g₁ ∙ emloop g₂) x}
             {f = app= (swap-transp-emloop g₁g₂ ∙ ap emloop-transp (emloop-comp g₁ g₂))}
             {g = app= (ap transp-emloop (emloop-comp g₁ g₂) ∙ λ= swap-transp-emloop-2)} $ λ h →
          app= (swap-transp-emloop g₁g₂ ∙ ap emloop-transp (emloop-comp g₁ g₂)) h
            =⟨ ap-∙ (λ k → k h) (swap-transp-emloop g₁g₂) (ap emloop-transp (emloop-comp g₁ g₂)) ⟩
          app= (swap-transp-emloop g₁g₂) h ∙ app= (ap emloop-transp (emloop-comp g₁ g₂)) h
            =⟨ =ₛ-out (DD h) ⟩
          app= (ap transp-emloop (emloop-comp g₁ g₂)) h ∙ app= (λ= swap-transp-emloop-2) h
            =⟨ ∙-ap (λ k → k h) (ap transp-emloop (emloop-comp g₁ g₂)) (λ= swap-transp-emloop-2) ⟩
          app= (ap transp-emloop (emloop-comp g₁ g₂) ∙ λ= swap-transp-emloop-2) h =∎

        FF : loop' g₁g₂ == ↓-→-from-transp (λ= swap-transp-emloop-2) [ Q ↓ emloop-comp g₁ g₂ ]
        FF = ap↓ ↓-→-from-transp $ ↓-='-in $
             swap-transp-emloop g₁g₂ ∙' ap emloop-transp (emloop-comp g₁ g₂)
               =⟨ ∙'=∙ (swap-transp-emloop g₁g₂) (ap emloop-transp (emloop-comp g₁ g₂)) ⟩
             swap-transp-emloop g₁g₂ ∙ ap emloop-transp (emloop-comp g₁ g₂)
               =⟨ EE ⟩
             ap transp-emloop (emloop-comp g₁ g₂) ∙ λ= swap-transp-emloop-2 =∎

        GG : ↓-→-from-transp (λ= swap-transp-emloop-2) == loop' g₁ ∙ᵈ loop' g₂
        GG = ↓-→-from-transp-∙ᵈ {B = fst ∘ Codes} {C = λ x → embase == x}
                                {p = emloop g₁} {q = emloop g₂}
                                {u = emloop} {u' = emloop} {u'' = emloop}
                                (swap-transp-emloop g₁) (swap-transp-emloop g₂)

        loop'-comp : loop' g₁g₂ == (loop' g₁ ∙ᵈ loop' g₂) [ Q ↓ emloop-comp g₁ g₂ ]
        loop'-comp = FF ▹ GG

    decode : {x : EM₁ G} → fst (Codes x) → embase == x
    decode {x} =
      EM₁-level₁-elim {P = Decode.P}
        emloop
        Decode.loop'
        Decode.loop'-comp
        x

    decode-encode : ∀ {x} (α : embase' G == x) → decode (encode α) == α
    decode-encode idp = emloop-ident {G = G}

    emloop-equiv : G.El ≃ (embase' G == embase)
    emloop-equiv = equiv emloop encode decode-encode encode-emloop

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
