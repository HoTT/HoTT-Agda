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

    Codes : EM₁ G → 0 -Type i
    Codes = EM₁-rec {G = G} {C = 0 -Type i}
                    (G.El , G.El-level)
                    Codes-hom

    abstract
      ↓-Codes-loop : ∀ g g' → g' == G.comp g' g [ fst ∘ Codes ↓ emloop g ]
      ↓-Codes-loop g g' =
        ↓-ap-out fst Codes (emloop g) $
        ↓-ap-out (idf _) fst (ap Codes (emloop g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ ap fst w ])
                  (! (EM₁Rec.emloop-β (G.El , G.El-level) Codes-hom g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ w ])
                  (! (fst=-β (ua $ comp-equiv g) _)) $
        ↓-idf-ua-in (comp-equiv g) idp


    encode : {x : EM₁ G} → embase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α G.ident

    encode-emloop : ∀ g → encode (emloop g) == g
    encode-emloop g = to-transp $
      transport (λ x → G.ident == x [ fst ∘ Codes ↓ emloop g ])
                 (G.unit-l g) (↓-Codes-loop g G.ident)

    decode : {x : EM₁ G} → fst (Codes x) → embase == x
    decode {x} =
      EM₁-elim {P = λ x' → fst (Codes x') → embase == x'}
        emloop
        loop'
        (λ _ _ → prop-has-all-paths-↓ {{↓-level ⟨⟩}})
        x
      where
      loop' : (g : G.El)
        → emloop == emloop [ (λ x' → fst (Codes x') → embase == x') ↓ emloop g ]
      loop' g = ↓-→-from-transp $ λ= $ λ y →
        transport (λ z → embase == z) (emloop g) (emloop y)
          =⟨ transp-cst=idf (emloop g) (emloop y) ⟩
        emloop y ∙ emloop g
          =⟨ ! (emloop-comp y g) ⟩
        emloop (G.comp y g)
          =⟨ ap emloop (! (to-transp (↓-Codes-loop g y))) ⟩
        emloop (transport (λ z → fst (Codes z)) (emloop g) y) =∎

    decode-encode : ∀ {x} (α : embase' G == x) → decode (encode α) == α
    decode-encode idp = emloop-ident {G = G}

    emloop-equiv : G.El ≃ (embase' G == embase)
    emloop-equiv = equiv emloop encode decode-encode encode-emloop

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
