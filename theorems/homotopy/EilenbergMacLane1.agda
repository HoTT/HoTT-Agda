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

      transp-emloop : embase' G == embase → G.El → embase' G == embase
      transp-emloop p = transport (λ x → embase' G == x) p ∘ emloop

      emloop-transp : embase' G == embase → G.El → embase' G == embase
      emloop-transp p = emloop ∘ transport (fst ∘ Codes) p

      module _ (g : G.El) where

        module _ (y : G.El) where

          transp-emloop=∙-emloop : transp-emloop (emloop g) y == emloop y ∙ emloop g
          transp-emloop=∙-emloop = transp-cst=idf (emloop g) (emloop y)

          emloop-comp=∙-emloop : emloop (G.comp y g) == emloop' G y ∙ emloop g
          emloop-comp=∙-emloop = emloop-comp y g

          emloop-comp=emloop-transp : emloop' G (G.comp y g) == emloop-transp (emloop' G g) y
          emloop-comp=emloop-transp = ap emloop (! (↓-Codes-loop-transp g y))

          transp-emloop=emloop-transp : transp-emloop (emloop g) y == emloop-transp (emloop g) y
          transp-emloop=emloop-transp = transp-emloop=∙-emloop ∙ ! emloop-comp=∙-emloop ∙ emloop-comp=emloop-transp

        swap-transp-emloop : transp-emloop (emloop g) == emloop-transp (emloop g)
        swap-transp-emloop = λ= transp-emloop=emloop-transp

        loop' : Q (emloop g)
        loop' = ↓-→-from-transp swap-transp-emloop

      module _ (g₁ g₂ : G.El) where

        g₁g₂ : G.El
        g₁g₂ = G.comp g₁ g₂

        swap-transp-emloop-2 : transp-emloop (emloop g₁ ∙ emloop g₂) == emloop-transp (emloop g₁ ∙ emloop g₂)
        swap-transp-emloop-2 = comp-transp {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop} {emloop} {emloop} (emloop g₁) (emloop g₂) (swap-transp-emloop g₁) (swap-transp-emloop g₂)

        f₁ : G.El → embase' G == embase
        f₁ = transp-emloop (emloop g₁g₂)

        f₂ : G.El → embase' G == embase
        f₂ = emloop-transp (emloop g₁ ∙ emloop g₂)

        f₅ : G.El → embase' G == embase
        f₅ = emloop-transp (emloop g₁g₂)

        f₆ : G.El → embase' G == embase
        f₆ = transp-emloop (emloop g₁ ∙ emloop g₂)

        q₁₅ : f₁ == f₅
        q₁₅ = swap-transp-emloop g₁g₂

        q₅₂ : f₅ == f₂
        q₅₂ = ap emloop-transp (emloop-comp g₁ g₂)

        q₁₂ : f₁ == f₂
        q₁₂ = q₁₅ ∙' q₅₂

        q₁₆ : f₁ == f₆
        q₁₆ = ap transp-emloop (emloop-comp g₁ g₂)

        q₆₂ : f₆ == f₂
        q₆₂ = swap-transp-emloop-2

        q₁₂' : f₁ == f₂
        q₁₂' = q₁₆ ∙ q₆₂

        module _ (y : G.El) where

          s₁ : embase' G == embase
          s₁ = f₁ y

          s₂ : embase' G == embase
          s₂ = f₂ y

          s₃ : embase' G == embase
          s₃ = emloop y ∙ emloop g₁g₂

          s₄ : embase' G == embase
          s₄ = emloop (G.comp y g₁g₂)

          s₅ : embase' G == embase
          s₅ = f₅ y

          s₆ : embase' G == embase
          s₆ = f₆ y

          s₇ : embase' G == embase
          s₇ = emloop y ∙ (emloop g₁ ∙ emloop g₂)

          s₈ : embase' G == embase
          s₈ = (emloop y ∙ emloop g₁) ∙ emloop g₂

          s₉ : embase' G == embase
          s₉ = emloop (G.comp y g₁) ∙ emloop g₂

          s₁₀ : embase' G == embase
          s₁₀ = emloop (G.comp (G.comp y g₁) g₂)

          e₁₂ : s₁ == s₂
          e₁₂ = app= q₁₂ y

          e₁₂' : s₁ == s₂
          e₁₂' = app= q₁₂' y

          e₁₃ : s₁ == s₃
          e₁₃ = transp-emloop=∙-emloop g₁g₂ y

          e₄₃ : s₄ == s₃
          e₄₃ = emloop-comp=∙-emloop g₁g₂ y

          e₄₅ : s₄ == s₅
          e₄₅ = emloop-comp=emloop-transp g₁g₂ y

          e₅₂ : s₅ == s₂
          e₅₂ = ap (λ p → emloop-transp p y) (emloop-comp g₁ g₂)

          e₁₆ : s₁ == s₆
          e₁₆ = ap (λ z → transp-emloop z y) (emloop-comp g₁ g₂)

          e₆₇ : s₆ == s₇
          e₆₇ = transp-cst=idf (emloop g₁ ∙ emloop g₂) (emloop y)

          e₃₇ : s₃ == s₇
          e₃₇ = ap (λ z → emloop y ∙ z) (emloop-comp g₁ g₂)

          e₈₇ : s₈ == s₇
          e₈₇ = ∙-assoc (emloop y) (emloop g₁) (emloop g₂)

          e₉₈ : s₉ == s₈
          e₉₈ = ap (λ p → p ∙ emloop g₂) (emloop-comp y g₁)

          e₁₀₋₉ : s₁₀ == s₉
          e₁₀₋₉ = emloop-comp (G.comp y g₁) g₂

          e₁₀₋₄ : s₁₀ == s₄
          e₁₀₋₄ = ap emloop (G.assoc y g₁ g₂)

          cd₁ : e₁₃ == e₁₆ ∙ e₆₇ ∙ ! e₃₇
          cd₁ = post-rearrange-in (e₁₃ ◃∎) (e₁₆ ◃∙ e₆₇ ◃∎) e₃₇ $
                transp-cst=idf-natural (emloop-comp g₁ g₂) (emloop y)

          cd₂ : ! e₃₇ ∙ ! e₄₃ == ! e₈₇ ∙ ! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄
          cd₂ = pre-rotate-in e₈₇ (! e₃₇ ∙ ! e₄₃) (! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄) $
                pre-rotate-in e₉₈ (e₈₇ ∙ ! e₃₇ ∙ ! e₄₃) (! e₁₀₋₉ ∙ e₁₀₋₄) $
                pre-rotate-in e₁₀₋₉ (e₉₈ ∙ e₈₇ ∙ ! e₃₇ ∙ ! e₄₃) e₁₀₋₄ $
                post-rearrange'-in (e₁₀₋₉ ◃∙ e₉₈ ◃∙ e₈₇ ◃∙ ! e₃₇ ◃∎) e₄₃ (e₁₀₋₄ ◃∎) $
                post-rearrange'-in (e₁₀₋₉ ◃∙ e₉₈ ◃∙ e₈₇ ◃∎) e₃₇ (e₁₀₋₄ ◃∙ e₄₃ ◃∎) $
                emloop-coh' G y g₁ g₂

          DD : e₁₂ == e₁₂'
          DD =
            e₁₂
              =⟨ ∙'=∙ q₁₅ q₅₂ |in-ctx (λ z → app= z y) ⟩
            app= (q₁₅ ∙ q₅₂) y
              =⟨ ap-∙ (λ g → g y) q₁₅ q₅₂ ⟩
            app= q₁₅ y ∙ app= q₅₂ y
              =⟨ ∘-ap (λ g → g y) emloop-transp (emloop-comp g₁ g₂) |in-ctx (λ z → app= q₁₅ y ∙ z) ⟩
            app= q₁₅ y ∙ e₅₂
              =⟨ app=-β {f = f₁} {g = f₅} (transp-emloop=emloop-transp g₁g₂) y |in-ctx (λ z → z ∙ e₅₂) ⟩
            (e₁₃ ∙ ! e₄₃ ∙ e₄₅) ∙ e₅₂
              =⟨ ! (↯-∙∙ (e₁₃ ◃∙ ! e₄₃ ◃∙ (e₄₅ ◃∎)) (e₅₂ ◃∎)) ⟩
            e₁₃ ∙ ! e₄₃ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (s₁ ∎∎) (e₁₃ ◃∎) (e₁₆ ◃∙ e₆₇ ◃∙ ! e₃₇ ◃∎) cd₁ (! e₄₃ ◃∙ e₄₅ ◃∙ e₅₂ ◃∎) ⟩
            e₁₆ ∙ e₆₇ ∙ ! e₃₇ ∙ ! e₄₃ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₇ ◃∎) (! e₃₇ ◃∙ ! e₄₃ ◃∎) (! e₈₇ ◃∙ ! e₉₈ ◃∙ ! e₁₀₋₉ ◃∙ e₁₀₋₄ ◃∎) cd₂ (e₄₅ ◃∙ e₅₂ ◃∎) ⟩
            e₁₆ ∙ e₆₇ ∙ ! e₈₇ ∙ ! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ {!!} ⟩
            e₁₂' =∎

        EE : q₁₂ == q₁₂'
        EE = –>-is-inj (app=-equiv {A = G.El} {P = λ _ → embase' G == embase} {f = f₁} {g = f₂})
                       q₁₂ q₁₂'
                       (λ= {A = G.El} {P = λ x → f₁ x == f₂ x} {f = e₁₂} {g = e₁₂'} DD)

        FF : loop' g₁g₂ == ↓-→-from-transp swap-transp-emloop-2 [ Q ↓ emloop-comp g₁ g₂ ]
        FF = foo (emloop-comp g₁ g₂) emloop emloop (swap-transp-emloop g₁g₂) swap-transp-emloop-2 EE

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
