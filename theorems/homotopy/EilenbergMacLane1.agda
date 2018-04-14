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
    Codes = EM₁-level₁-rec {G = G} {C = 0 -Type i}
                           (G.El , G.El-level)
                           Codes-hom

    abstract
      ↓-Codes-loop : ∀ g g' → g' == G.comp g' g [ fst ∘ Codes ↓ emloop g ]
      ↓-Codes-loop g g' =
        ↓-ap-out fst Codes (emloop g) $
        ↓-ap-out (idf _) fst (ap Codes (emloop g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ ap fst w ])
                  (! (EM₁Level₁Rec.emloop-β (G.El , G.El-level) Codes-hom g)) $
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


    -- TODO: move this elsewhere
    foo : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
      {x x' : A} {p₁ p₂ : x == x'} (q : p₁ == p₂)
      (u : B x → C x) (u' : B x' → C x')
      (s : transport C p₁ ∘ u == u' ∘ transport B p₁)
      (t : transport C p₂ ∘ u == u' ∘ transport B p₂)
      → (s ∙' ap (λ p → u' ∘ transport B p) q) == (ap (λ p → transport C p ∘ u) q ∙ t)
      -- → s == t [ (λ p → transport C p ∘ u == u' ∘ transport B p) ↓ q ]
      → ↓-→-from-transp s == ↓-→-from-transp t [ (λ p → u == u' [ (λ y → B y → C y) ↓ p ]) ↓ q ]
    foo q u u' s t h = ap↓ ↓-→-from-transp (↓-='-in h)
      -- ap↓ ↓-→-from-transp h
    module Decode where

      P : EM₁ G → Type i
      P x' = fst (Codes x') → embase == x'

      Q : embase' G == embase → Type i
      Q p = emloop == emloop [ P ↓ p ]

      transport-emloop : embase' G == embase → G.El → embase' G == embase
      transport-emloop p = transport (λ x → embase' G == x) p ∘ emloop

      emloop-transport : embase' G == embase → G.El → embase' G == embase
      emloop-transport p = emloop ∘ transport (fst ∘ Codes) p

      abstract
        loop'-transp : (g : G.El) → transport-emloop (emloop g) == emloop-transport (emloop g)
        loop'-transp g = λ= $ λ y →
          transport (λ z → embase == z) (emloop g) (emloop y)
            =⟨ transp-cst=idf (emloop g) (emloop y) ⟩
          emloop y ∙ emloop g
            =⟨ ! (emloop-comp y g) ⟩
          emloop (G.comp y g)
            =⟨ ap emloop (! (↓-Codes-loop-transp g y)) ⟩
          emloop (transport (fst ∘ Codes) (emloop g) y) =∎

      -- takes about one second to check
      loop' : (g : G.El) → Q (emloop g)
      loop' g = ↓-→-from-transp (loop'-transp g)

      module _ (g₁ g₂ : G.El) where

        g₁g₂ : G.El
        g₁g₂ = G.comp g₁ g₂

        comp-loop'-transp : transport-emloop (emloop g₁ ∙ emloop g₂) == emloop-transport (emloop g₁ ∙ emloop g₂)
        comp-loop'-transp = comp-transp {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop} {emloop} {emloop} (emloop g₁) (emloop g₂) (loop'-transp g₁) (loop'-transp g₂)

        f₁ : G.El → embase' G == embase
        f₁ = transport-emloop (emloop' G g₁g₂)

        f₂ : G.El → embase' G == embase
        f₂ = emloop-transport (emloop' G g₁ ∙ emloop' G g₂)

        f₁=f₂ : f₁ == f₂
        f₁=f₂ = loop'-transp g₁g₂ ∙' ap emloop-transport (emloop-comp g₁ g₂)

        f₁=f₂' : f₁ == f₂
        f₁=f₂' = ap transport-emloop (emloop-comp g₁ g₂) ∙ comp-loop'-transp

        module _ (y : G.El) where

          s₀ : embase' G == embase
          s₀ = transport-emloop (emloop g₁ ∙ emloop g₂) y

          s₁ : embase' G == embase
          s₁ = transport-emloop (emloop g₁g₂) y

          s₂ : embase' G == embase
          s₂ = emloop y ∙ emloop g₁g₂

          s₃ : embase' G == embase
          s₃ = emloop (G.comp y g₁g₂)

          s₄ : embase' G == embase
          s₄ = emloop-transport (emloop g₁g₂) y

          s₅ : embase' G == embase
          s₅ = emloop-transport (emloop g₁ ∙ emloop g₂) y

          s₆ : embase' G == embase
          s₆ = emloop y ∙ (emloop g₁ ∙ emloop g₂)

          e₀₆ : s₀ == s₆
          e₀₆ = transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop y)

          e₁₂ : s₁ == s₂
          e₁₂ = transp-cst=idf (emloop g₁g₂) (emloop y)

          e₂₃ : s₂ == s₃
          e₂₃ = ! (emloop-comp y g₁g₂)

          e₃₄ : s₃ == s₄
          e₃₄ = ap emloop (! (↓-Codes-loop-transp g₁g₂ y))

          e₄₅ : s₄ == s₅
          e₄₅ = ap (λ p → emloop-transport p y) (emloop-comp g₁ g₂)

          e₁₅ : s₁ == s₅
          e₁₅ = app= f₁=f₂  y

          e₁₅' : s₁ == s₅
          e₁₅' = app= (ap transport-emloop (emloop-comp g₁ g₂) ∙ comp-loop'-transp) y

          DD : e₁₅ == e₁₅'
          DD = {!!}

        EE : f₁=f₂ == f₁=f₂'
        EE = –>-is-inj (app=-equiv {A = G.El} {P = λ _ → embase' G == embase} {f = f₁} {g = f₂})
                       f₁=f₂ f₁=f₂'
                       (λ= {A = G.El} {P = λ x → f₁ x == f₂ x} {f = e₁₅} {g = e₁₅'} DD)

        FF : loop' g₁g₂ == ↓-→-from-transp comp-loop'-transp [ Q ↓ emloop-comp g₁ g₂ ]
        FF = foo (emloop-comp g₁ g₂) emloop emloop (loop'-transp g₁g₂) comp-loop'-transp EE

{-
        GG : ↓-→-from-transp comp-loop'-transp == loop' g₁ ∙ᵈ loop' g₂
        GG = ↓-→-from-transp-∙ᵈ {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop g₁} {emloop g₂} {emloop} {emloop} {emloop} (loop'-transp g₁) (loop'-transp g₂)

        loop'-comp : loop' g₁g₂ == (loop' g₁ ∙ᵈ loop' g₂) [ Q ↓ emloop-comp g₁ g₂ ]
        loop'-comp = FF ▹ GG

    decode : {x : EM₁ G} → fst (Codes x) → embase == x
    decode {x} =
      EM₁-elim {P = Decode.P}
        emloop
        Decode.loop'
        Decode.loop'-comp
        (λ g₁ g₂ g₃ → prop-has-all-paths-↓ {{↓-level (↓-level (Π-level {A = G.El} {B = λ _ → embase' G == embase} (λ _ → ⟨⟩)))}})
        x
      where

    decode-encode : ∀ {x} (α : embase' G == x) → decode (encode α) == α
    decode-encode idp = emloop-ident {G = G}

    emloop-equiv : G.El ≃ (embase' G == embase)
    emloop-equiv = equiv emloop encode decode-encode encode-emloop
    -}

  -- Ω¹-EM₁ : Ω^S-group 0 (⊙EM₁ G) ≃ᴳ G
  -- Ω¹-EM₁ = ≃-to-≃ᴳ (emloop-equiv ⁻¹)
  --   (λ l₁ l₂ → <– (ap-equiv emloop-equiv _ _) $
  --     emloop (encode (l₁ ∙ l₂))
  --       =⟨ decode-encode (l₁ ∙ l₂) ⟩
  --     l₁ ∙ l₂
  --       =⟨ ! $ ap2 _∙_ (decode-encode l₁) (decode-encode l₂) ⟩
  --     emloop (encode l₁) ∙ emloop (encode l₂)
  --       =⟨ ! $ emloop-comp (encode l₁) (encode l₂) ⟩
  --     emloop (G.comp (encode l₁) (encode l₂))
  --       =∎)

  -- π₁-EM₁ : πS 0 (⊙EM₁ G) ≃ᴳ G
  -- π₁-EM₁ = Ω¹-EM₁ ∘eᴳ unTrunc-iso (Ω^S-group-structure 0 (⊙EM₁ G))
