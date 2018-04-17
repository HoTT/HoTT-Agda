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

    module Decode where

      P : EM₁ G → Type i
      P x' = fst (Codes x') → embase == x'

      Q : embase' G == embase → Type i
      Q p = emloop == emloop [ P ↓ p ]

      {- transport in path fibration of EM₁ -}
      transp-PF : embase' G == embase → embase' G == embase → embase' G == embase
      transp-PF = transport (λ x → embase' G == x)

      {- transport in Codes -}
      transp-C : embase' G == embase → G.El → G.El
      transp-C = transport (fst ∘ Codes)

      transp-emloop : embase' G == embase → G.El → embase' G == embase
      transp-emloop p = transp-PF p ∘ emloop

      emloop-transp : embase' G == embase → G.El → embase' G == embase
      emloop-transp p = emloop ∘ transp-C p

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

        swap-transp-emloop-2 : transp-emloop (emloop g₁ ∙ emloop g₂) ∼ emloop-transp (emloop g₁ ∙ emloop g₂)
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
        q₆₂ = λ= swap-transp-emloop-2

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

          s₁₁ : embase' G == embase
          s₁₁ = transp-PF (emloop g₂) (emloop y ∙ emloop g₁)

          s₁₂ : embase' G == embase
          s₁₂ = transp-emloop (emloop g₂) (G.comp y g₁)

          s₁₃ : embase' G == embase
          s₁₃ = transp-PF (emloop g₂) (transp-emloop (emloop g₁) y)

          s₁₄ : embase' G == embase
          s₁₄ = emloop-transp (emloop g₂) (transp-C (emloop g₁) y)

          s₁₅ : embase' G == embase
          s₁₅ = transp-emloop (emloop g₂) (transp-C (emloop g₁) y)
          --  = transp-PF (emloop g₂) (emloop-transp (emloop g₁) y)

          s₁₆ : embase' G == embase
          s₁₆ = emloop-transp (emloop g₁) y ∙ emloop g₂

          s₁₇ : embase' G == embase
          s₁₇ = emloop (G.comp (transp-C (emloop g₁) y) g₂)

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

          e₁₁₋₈ : s₁₁ == s₈
          e₁₁₋₈ = transp-cst=idf (emloop g₂) (emloop y ∙ emloop g₁)

          e₁₂₋₁₁ : s₁₂ == s₁₁
          e₁₂₋₁₁ = ap (transp-PF (emloop g₂)) (emloop-comp y g₁)

          e₁₂₋₉ : s₁₂ == s₉
          e₁₂₋₉ = transp-emloop=∙-emloop g₂ (G.comp y g₁)

          e₁₃₋₁₁ : s₁₃ == s₁₁
          e₁₃₋₁₁ = ap (λ z → transp-PF (emloop g₂) z) (transp-emloop=∙-emloop g₁ y)

          e₆₋₁₃ : s₆ == s₁₃
          e₆₋₁₃ = transp-∙ (emloop g₁) (emloop g₂) (emloop y)

          e₂₋₁₄ : s₂ == s₁₄
          e₂₋₁₄ = ap emloop (transp-∙ (emloop g₁) (emloop g₂) y)

          e₁₃₋₁₅ : s₁₃ == s₁₅
          e₁₃₋₁₅ = ap (transp-PF (emloop g₂)) (transp-emloop=emloop-transp g₁ y)

          e₁₃₋₁₅' : s₁₃ == s₁₅
          e₁₃₋₁₅' = ap (transp-PF (emloop g₂)) (app= (swap-transp-emloop g₁) y)

          e₁₂₋₁₅ : s₁₂ == s₁₅
          e₁₂₋₁₅ = ap (transp-emloop (emloop g₂)) (! (↓-Codes-loop-transp g₁ y))

          e₁₃₋₁₅'=e₁₃₋₁₅ : e₁₃₋₁₅' == e₁₃₋₁₅
          e₁₃₋₁₅'=e₁₃₋₁₅ =
            ap (ap (transp-PF (emloop g₂)))
               (app=-β {f = transp-emloop (emloop g₁)} {g = emloop-transp (emloop g₁)}
                       (transp-emloop=emloop-transp g₁) y)

          e₁₅₋₁₄ : s₁₅ == s₁₄
          e₁₅₋₁₄ = transp-emloop=emloop-transp g₂ (transp-C (emloop g₁) y)

          e₁₅₋₁₄' : s₁₅ == s₁₄
          e₁₅₋₁₄' = app= (λ= (transp-emloop=emloop-transp g₂)) (transp-C (emloop g₁) y)

          e₁₅₋₁₄'=e₁₅₋₁₄ : e₁₅₋₁₄' == e₁₅₋₁₄
          e₁₅₋₁₄'=e₁₅₋₁₄ =
            app=-β {f = transp-emloop (emloop g₂)} {g = emloop-transp (emloop g₂)}
                   (transp-emloop=emloop-transp g₂) (transp-C (emloop g₁) y)

          e₁₅₋₁₆ : s₁₅ == s₁₆
          e₁₅₋₁₆ = transp-emloop=∙-emloop g₂ (transp-C (emloop g₁) y)

          e₁₇₋₁₆ : s₁₇ == s₁₆
          e₁₇₋₁₆ = emloop-comp (transp-C (emloop g₁) y) g₂

          e₁₇₋₁₄ : s₁₇ == s₁₄
          e₁₇₋₁₄ = emloop-comp=emloop-transp g₂ (transp-C (emloop g₁) y)

          e₁₀₋₁₇ : s₁₀ == s₁₇
          e₁₀₋₁₇ = ap (λ z → emloop (G.comp z g₂)) (! (↓-Codes-loop-transp g₁ y))

          e₉₋₁₆ : s₉ == s₁₆
          e₉₋₁₆ = ap (λ z → emloop z ∙ emloop g₂) (! (↓-Codes-loop-transp g₁ y))

          -- TODO: move this somewhere else?
          ap-natural : ∀ {j k} {A : Type j} {B : Type k} {f g : A → B}
            {a a' : A} (p : a == a') (h : (x : A) → f x == g x)
            → ap f p ∙ h a' == h a ∙ ap g p
          ap-natural {f = f} {g = g} {a = a} {a' = a'} p h =
            ∙=∙' (ap f p) (h a') ∙ ! (↓-='-out' {f = f} {g = g} {p = p} {u = h a} {v = h a'} (apd h p))

          cd₁ : e₁₃ == e₁₆ ∙ e₆₇ ∙ ! e₃₇
          cd₁ = post-rearrange-in (e₁₃ ◃∎) (e₁₆ ◃∙ e₆₇ ◃∎) e₃₇ $
                ! (ap-natural (emloop-comp g₁ g₂) (λ p → transp-cst=idf p (emloop y)))

          cd₂ : ! e₃₇ ∙ ! e₄₃ == ! e₈₇ ∙ ! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄
          cd₂ = pre-rotate-in (! e₃₇ ∙ ! e₄₃) e₈₇ (! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄) $
                pre-rotate-in (e₈₇ ∙ ! e₃₇ ∙ ! e₄₃) e₉₈ (! e₁₀₋₉ ∙ e₁₀₋₄) $
                pre-rotate-in (e₉₈ ∙ e₈₇ ∙ ! e₃₇ ∙ ! e₄₃) e₁₀₋₉ e₁₀₋₄ $
                post-rearrange'-in (e₁₀₋₉ ◃∙ e₉₈ ◃∙ e₈₇ ◃∙ ! e₃₇ ◃∎) e₄₃ (e₁₀₋₄ ◃∎) $
                post-rearrange'-in (e₁₀₋₉ ◃∙ e₉₈ ◃∙ e₈₇ ◃∎) e₃₇ (e₁₀₋₄ ◃∙ e₄₃ ◃∎) $
                emloop-coh' G y g₁ g₂

          cd₃ : e₆₇ ∙ ! e₈₇ == e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ e₁₁₋₈
          cd₃ = post-rearrange'-in (e₆₇ ◃∎) e₈₇ (e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∙ e₁₁₋₈ ◃∎) $
                transp-cst=idf-pentagon (emloop g₁) (emloop g₂) (emloop y)

          cd₄ : e₁₁₋₈ ∙ ! e₉₈ == ! e₁₂₋₁₁ ∙ e₁₂₋₉
          cd₄ = pre-rotate-in (e₁₁₋₈ ∙ ! e₉₈) e₁₂₋₁₁ e₁₂₋₉ $
                post-rearrange'-in (e₁₂₋₁₁ ◃∙ e₁₁₋₈ ◃∎) e₉₈ (e₁₂₋₉ ◃∎) $
                ap-natural (emloop-comp' G y g₁) (transp-cst=idf (emloop g₂))

          cd₅ : ! e₁₀₋₉ == e₉₋₁₆ ∙ ! e₁₇₋₁₆ ∙ ! e₁₀₋₁₇
          cd₅ = post-rearrange-in (! e₁₀₋₉ ◃∎) (e₉₋₁₆ ◃∙ ! e₁₇₋₁₆ ◃∎) e₁₀₋₁₇ $
                post-rearrange-in (! e₁₀₋₉ ◃∙ e₁₀₋₁₇ ◃∎) (e₉₋₁₆ ◃∎) e₁₇₋₁₆ $
                pre-rotate'-in e₁₀₋₉ (e₁₀₋₁₇ ∙ e₁₇₋₁₆) e₉₋₁₆ $
                ap-natural {A = G.El} {B = embase' G == embase}
                            {f = λ (z : G.El) → emloop (G.comp z g₂)}
                            {g = λ (z : G.El) → emloop z ∙ emloop g₂}
                            {a = G.comp y g₁} {a' = transp-C (emloop g₁) y}
                            (! (↓-Codes-loop-transp g₁ y)) (λ (z : G.El) → emloop-comp' G z g₂)

          cd₆ : ! e₁₀₋₁₇ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂ == e₁₇₋₁₄ ∙ ! e₂₋₁₄
          cd₆ =
            ! e₁₀₋₁₇ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ (ap (λ p → ! p) (ap-∘ emloop (λ z → G.comp z g₂) (! (↓-Codes-loop-transp g₁ y))) ∙ !-ap emloop i₁₀₋₁₇) |in-ctx (λ z → z ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂) ⟩
            ap emloop (! i₁₀₋₁₇) ∙ ap emloop i₁₀₋₄ ∙ ap emloop i₄₅ ∙ e₅₂
              =⟨ e₅₂=ap-emloop-i₅₂ |in-ctx (λ (z : s₅ == s₂) → ap emloop (! i₁₀₋₁₇) ∙ ap emloop i₁₀₋₄ ∙ ap emloop i₄₅ ∙ z) ⟩
            ap emloop (! i₁₀₋₁₇) ∙ ap emloop i₁₀₋₄ ∙ ap emloop i₄₅ ∙ ap emloop i₅₂
              =⟨ ! (ap-∙∙∙ emloop (! i₁₀₋₁₇) i₁₀₋₄ i₄₅ i₅₂) ⟩
            ap emloop (! i₁₀₋₁₇ ∙ i₁₀₋₄ ∙ i₄₅ ∙ i₅₂)
              =⟨ ap (ap emloop) cd₆' ⟩
            ap emloop (i₁₇₋₁₄ ∙ ! i₂₋₁₄)
              =⟨ ap-∙ emloop i₁₇₋₁₄ (! i₂₋₁₄) ⟩
            ap emloop i₁₇₋₁₄ ∙ ap emloop (! i₂₋₁₄)
              =⟨ ap-! emloop i₂₋₁₄ |in-ctx (λ z → e₁₇₋₁₄ ∙ z) ⟩
            e₁₇₋₁₄ ∙ ! e₂₋₁₄ =∎
            where
              h₁₇ : G.El
              h₁₇ = G.comp (transp-C (emloop g₁) y) g₂
              h₁₀ : G.El
              h₁₀ = G.comp (G.comp y g₁) g₂
              h₄ : G.El
              h₄ = G.comp y (G.comp g₁ g₂)
              h₅ : G.El
              h₅ = transp-C (emloop (G.comp g₁ g₂)) y
              h₂ : G.El
              h₂ = transp-C (emloop g₁ ∙ emloop g₂) y
              h₁₄ : G.El
              h₁₄ = transp-C (emloop g₂) (transp-C (emloop g₁) y)
              i₁₀₋₁₇ : h₁₀ == h₁₇
              i₁₀₋₁₇ = ap (λ z → G.comp z g₂) (! (↓-Codes-loop-transp g₁ y))
              i₁₀₋₄ : h₁₀ == h₄
              i₁₀₋₄ = G.assoc y g₁ g₂
              i₄₅ : h₄ == h₅
              i₄₅ = ! (↓-Codes-loop-transp g₁g₂ y)
              i₅₂ : h₅ == h₂
              i₅₂ = ap (λ p → transp-C p y) (emloop-comp g₁ g₂)
              i₁₇₋₁₄ : h₁₇ == h₁₄
              i₁₇₋₁₄ = ! (↓-Codes-loop-transp g₂ (transp-C (emloop g₁) y))
              i₂₋₁₄ : h₂ == h₁₄
              i₂₋₁₄ = transp-∙ (emloop g₁) (emloop g₂) y
              e₅₂=ap-emloop-i₅₂ : e₅₂ == ap emloop i₅₂
              e₅₂=ap-emloop-i₅₂ = ap-∘ (emloop' G) (λ p → transp-C p y) (emloop-comp g₁ g₂)
              cd₆' : ! i₁₀₋₁₇ ∙ i₁₀₋₄ ∙ i₄₅ ∙ i₅₂ == i₁₇₋₁₄ ∙ ! i₂₋₁₄
              cd₆' = prop-path (has-level-apply G.El-level h₁₇ h₂) _ _

          cd₇ : e₁₂₋₉ ∙ e₉₋₁₆ == e₁₂₋₁₅ ∙ e₁₅₋₁₆
          cd₇ = ! (ap-natural {f = transp-emloop (emloop g₂)}
                              {g = λ (z : G.El) → emloop z ∙ emloop g₂}
                              (! (↓-Codes-loop-transp g₁ y))
                              (transp-emloop=∙-emloop g₂))

          cd₈ : e₁₃₋₁₁ ∙ ! e₁₂₋₁₁ ∙ e₁₂₋₁₅ == e₁₃₋₁₅
          cd₈ = {!!}

          -- e₁₃₋₁₁ : s₁₃ == s₁₁
          -- e₁₃₋₁₁ = ap (λ z → transp-PF (emloop g₂) z) (transp-emloop=∙-emloop g₁ y)

          -- e₁₂₋₁₁ : s₁₂ == s₁₁
          -- e₁₂₋₁₁ = ap (transp-PF (emloop g₂)) (emloop-comp y g₁)

          -- e₁₂₋₁₅ : s₁₂ == s₁₅
          -- e₁₂₋₁₅ = ap (transp-emloop (emloop g₂)) (! (↓-Codes-loop-transp g₁ y))

          -- e₁₃₋₁₅ : s₁₃ == s₁₅
          -- e₁₃₋₁₅ = ap (transp-PF (emloop g₂)) (transp-emloop=emloop-transp g₁ y)

          cd₉ : e₁₅₋₁₆ ∙ ! e₁₇₋₁₆ ∙ e₁₇₋₁₄ == e₁₅₋₁₄
          cd₉ = {!!}

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
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₇ ◃∎)
                              (! e₃₇ ◃∙ ! e₄₃ ◃∎) (! e₈₇ ◃∙ ! e₉₈ ◃∙ ! e₁₀₋₉ ◃∙ e₁₀₋₄ ◃∎) cd₂
                              (e₄₅ ◃∙ e₅₂ ◃∎) ⟩
            e₁₆ ∙ e₆₇ ∙ ! e₈₇ ∙ ! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (e₁₆ ◃∎)
                              (e₆₇ ◃∙ ! e₈₇ ◃∎) (e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∙ e₁₁₋₈ ◃∎) cd₃
                              (! e₉₈ ◃∙ ! e₁₀₋₉ ◃∙ e₁₀₋₄ ◃∙ e₄₅ ◃∙ e₅₂ ◃∎) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ e₁₁₋₈ ∙ ! e₉₈ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∎)
                              (e₁₁₋₈ ◃∙ ! e₉₈ ◃∎) (! e₁₂₋₁₁ ◃∙ e₁₂₋₉ ◃∎) cd₄
                              (! e₁₀₋₉ ◃∙ e₁₀₋₄ ◃∙ e₄₅ ◃∙ e₅₂ ◃∎)  ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ ! e₁₂₋₁₁ ∙ e₁₂₋₉ ∙ ! e₁₀₋₉ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∙ ! e₁₂₋₁₁ ◃∙ e₁₂₋₉ ◃∎)
                              (! e₁₀₋₉ ◃∎) (e₉₋₁₆ ◃∙ ! e₁₇₋₁₆ ◃∙ ! e₁₀₋₁₇ ◃∎) cd₅
                              (e₁₀₋₄ ◃∙ e₄₅ ◃∙ e₅₂ ◃∎)  ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ ! e₁₂₋₁₁ ∙ e₁₂₋₉ ∙ e₉₋₁₆ ∙ ! e₁₇₋₁₆ ∙ ! e₁₀₋₁₇ ∙ e₁₀₋₄ ∙ e₄₅ ∙ e₅₂
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∙ ! e₁₂₋₁₁ ◃∙ e₁₂₋₉ ◃∙ e₉₋₁₆ ◃∙ ! e₁₇₋₁₆ ◃∎)
                              (! e₁₀₋₁₇ ◃∙ e₁₀₋₄ ◃∙ e₄₅ ◃∙ e₅₂ ◃∎) (e₁₇₋₁₄ ◃∙ ! e₂₋₁₄ ◃∎) cd₆ (s₂ ∎∎) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ ! e₁₂₋₁₁ ∙ e₁₂₋₉ ∙ e₉₋₁₆ ∙ ! e₁₇₋₁₆ ∙ e₁₇₋₁₄ ∙ ! e₂₋₁₄
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∙ e₁₃₋₁₁ ◃∙ ! e₁₂₋₁₁ ◃∎) (e₁₂₋₉ ◃∙ e₉₋₁₆ ◃∎) (e₁₂₋₁₅ ◃∙ e₁₅₋₁₆ ◃∎) cd₇ (! e₁₇₋₁₆ ◃∙ e₁₇₋₁₄ ◃∙ ! e₂₋₁₄ ◃∎) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₁ ∙ ! e₁₂₋₁₁ ∙ e₁₂₋₁₅ ∙ e₁₅₋₁₆ ∙ ! e₁₇₋₁₆ ∙ e₁₇₋₁₄ ∙ ! e₂₋₁₄
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∎) (e₁₃₋₁₁ ◃∙ ! e₁₂₋₁₁ ◃∙ e₁₂₋₁₅ ◃∎) (e₁₃₋₁₅ ◃∎) cd₈ (e₁₅₋₁₆ ◃∙ ! e₁₇₋₁₆ ◃∙ e₁₇₋₁₄ ◃∙ ! e₂₋₁₄ ◃∎) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₅ ∙ e₁₅₋₁₆ ∙ ! e₁₇₋₁₆ ∙ e₁₇₋₁₄ ∙ ! e₂₋₁₄
              =⟨ rewrite-path (e₁₆ ◃∙ e₆₋₁₃ ◃∙ e₁₃₋₁₅ ◃∎) (e₁₅₋₁₆ ◃∙ ! e₁₇₋₁₆ ◃∙ e₁₇₋₁₄ ◃∎) (e₁₅₋₁₄ ◃∎) cd₉ (! e₂₋₁₄ ◃∎) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₅ ∙ e₁₅₋₁₄ ∙ ! e₂₋₁₄
              =⟨ ap2 (λ x y → e₁₆ ∙ e₆₋₁₃ ∙ x ∙ y ∙ ! e₂₋₁₄) (! e₁₃₋₁₅'=e₁₃₋₁₅) (! e₁₅₋₁₄'=e₁₅₋₁₄) ⟩
            e₁₆ ∙ e₆₋₁₃ ∙ e₁₃₋₁₅' ∙ e₁₅₋₁₄' ∙ ! e₂₋₁₄
              =⟨ ! (app=-β {f = f₆} {g = f₂} swap-transp-emloop-2 y) |in-ctx (λ z → e₁₆ ∙ z) ⟩
            e₁₆ ∙ app= q₆₂ y
              =⟨ ap-∘ (λ g → g y) transp-emloop (emloop-comp g₁ g₂) |in-ctx (λ z → z ∙ app= q₆₂ y) ⟩
            app= q₁₆ y ∙ app= q₆₂ y
              =⟨ ∙-ap (λ g → g y) q₁₆ q₆₂ ⟩
            e₁₂' =∎

        {-
        EE : q₁₂ == q₁₂'
        EE = –>-is-inj (app=-equiv {A = G.El} {P = λ _ → embase' G == embase} {f = f₁} {g = f₂})
                       q₁₂ q₁₂'
                       (λ= {A = G.El} {P = λ x → f₁ x == f₂ x} {f = e₁₂} {g = e₁₂'} DD)

        FF : loop' g₁g₂ == ↓-→-from-transp q₆₂ [ Q ↓ emloop-comp g₁ g₂ ]
        FF = foo (emloop-comp g₁ g₂) emloop emloop (swap-transp-emloop g₁g₂) q₆₂ EE

        GG : ↓-→-from-transp (λ= swap-transp-emloop-2) == loop' g₁ ∙ᵈ loop' g₂
        GG = ↓-→-from-transp-∙ᵈ {i} {i} {i} {EM₁ G} {fst ∘ Codes} {λ x → embase == x} {embase} {embase} {embase} {emloop g₁} {emloop g₂} {emloop} {emloop} {emloop} (swap-transp-emloop g₁) (swap-transp-emloop g₂)

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
