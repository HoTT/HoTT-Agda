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

    decode : {x : EM₁ G} → fst (Codes x) → embase == x
    decode {x} =
      EM₁-elim {P = P}
        emloop
        loop'
        loop'-comp
        x
      where
      P : EM₁ G → Type i
      P x' = fst (Codes x') → embase == x'
      loop'-transp : (g : G.El)
        → transport (λ x → embase' G == x) (emloop g) ∘ emloop == emloop ∘ transport (fst ∘ Codes) (emloop g)
      loop'-transp g = λ= $ λ y →
        transport (λ z → embase == z) (emloop g) (emloop y)
          =⟨ transp-cst=idf (emloop g) (emloop y) ⟩
        emloop y ∙ emloop g
          =⟨ ! (emloop-comp y g) ⟩
        emloop (G.comp y g)
          =⟨ ap emloop (! (to-transp (↓-Codes-loop g y))) ⟩
        emloop (transport (λ z → fst (Codes z)) (emloop g) y) =∎
      Q : embase' G == embase → Type i
      Q p = emloop == emloop [ P ↓ p ]
      loop' : (g : G.El) → Q (emloop g)
      loop' g = ↓-→-from-transp (loop'-transp g)
      comp-loop'-transp : (g₁ g₂ : G.El)
        → transport (λ x → embase' G == x) (emloop g₁ ∙ emloop g₂) ∘ emloop == emloop ∘ transport (fst ∘ Codes) (emloop g₁ ∙ emloop g₂)
      comp-loop'-transp g₁ g₂ = comp-transp {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop} {emloop} {emloop} (emloop g₁) (emloop g₂) (loop'-transp g₁) (loop'-transp g₂)
      EE : (g₁ g₂ : G.El) →
           loop'-transp (G.comp g₁ g₂) ∙' ap (λ p → emloop ∘ transport (fst ∘ Codes) p) (emloop-comp g₁ g₂) ==
           ap (λ p → transport (λ x → embase' G == x) p ∘ emloop) (emloop-comp g₁ g₂) ∙ comp-loop'-transp g₁ g₂
      EE g₁ g₂ = {!!}
      FF : (g₁ g₂ : G.El) → loop' (G.comp g₁ g₂) == ↓-→-from-transp (comp-loop'-transp g₁ g₂) [ Q ↓ emloop-comp g₁ g₂ ]
      FF g₁ g₂ = foo (emloop-comp g₁ g₂) emloop emloop (loop'-transp (G.comp g₁ g₂)) (comp-loop'-transp g₁ g₂) (EE g₁ g₂)
      GG : (g₁ g₂ : G.El) → ↓-→-from-transp (comp-loop'-transp g₁ g₂) == loop' g₁ ∙ᵈ loop' g₂
      GG g₁ g₂ = ↓-→-from-transp-∙ᵈ {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop g₁} {emloop g₂} {emloop} {emloop} {emloop} (loop'-transp g₁) (loop'-transp g₂)
      loop'-comp : (g₁ g₂ : G.El) → loop' (G.comp g₁ g₂) == (loop' g₁ ∙ᵈ loop' g₂) [ Q ↓ emloop-comp g₁ g₂ ]
      loop'-comp g₁ g₂ = FF g₁ g₂ ▹ GG g₁ g₂ -- ? ▹ (↓-→-from-transp-∙ᵈ (loop'-transp g₁) (loop'-transp g₂))
        {-from-transp Q (emloop-comp' G g₁ g₂) $
        transport Q (emloop-comp' G g₁ g₂) (loop' (G.comp g₁ g₂))
          =⟨ {!!} ⟩
        -- ↓-→-from-transp (comp-transp (emloop' G g₁) (emloop' G g₂) (loop'-transp g₁) (loop'-transp g₂))
        --  =⟨ ↓-→-from-transp-∙ᵈ (loop'-transp g₁) (loop'-transp g₂) ⟩
        loop' g₁ ∙ᵈ loop' g₂ =∎

        -- {!!} ∙ ↓-→-from-transp-∙ᵈ (loop'-transp g₁) (loop'-transp g₂)
        -}

    decode-encode : ∀ {x} (α : embase' G == x) → decode (encode α) == α
    decode-encode idp = emloop-ident {G = G}

    emloop-equiv : G.El ≃ (embase' G == embase)
    emloop-equiv = equiv emloop encode decode-encode encode-emloop

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
