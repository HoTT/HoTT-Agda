{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalences2
open import lib.NConnected
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Group
open import lib.types.Pointed
open import lib.groups.LoopSpace
open import lib.groups.Homomorphisms
open import lib.groups.HomotopyGroup

module lib.types.EilenbergMacLane1 where

module EM₁ {i} (G : Group i) where

  module G = Group G

  private
    data #EM₁-aux : Type i where
      #embase : #EM₁-aux

    data #EM₁ : Type i where
      #em₁ : #EM₁-aux → (Unit → Unit) → #EM₁

  EM₁ : Type i
  EM₁ = #EM₁

  embase : EM₁
  embase = #em₁ #embase _

  ⊙EM₁ : Ptd i
  ⊙EM₁ = ⊙[ EM₁ , embase ]

  postulate  -- HIT
    emlevel : has-level ⟨ 1 ⟩ EM₁
    emloop : G.El → embase == embase
    emloop-comp : ∀ g₁ g₂ → emloop (G.comp g₁ g₂) == emloop g₁ ∙ emloop g₂
  emloop-ident : emloop G.ident == idp
  emloop-ident = ! $ anti-whisker-right (emloop G.ident) $
    ap emloop (! $ G.unit-r G.ident) ∙ emloop-comp G.ident G.ident

  module EM₁Rec {j} {C : Type j}
    (C-level : has-level ⟨ 1 ⟩ C)
    (embase* : C)
    (hom* : G →ᴳ (Ω^S-group 0 (C , embase*) C-level)) where

    -- XXX Should be defined in terms of the dependent one.
    f : EM₁ → C
    f = f-aux phantom  where

      f-aux : Phantom hom* → (EM₁ → C)
      f-aux phantom (#em₁ #embase _) = embase*

    postulate  -- HIT
      emloop-β : (g : G.El) → ap f (emloop g) == GroupHom.f hom* g

  open EM₁Rec public using () renaming (f to EM₁-rec)

  module EM₁Elim {j} {P : EM₁ → Type j}
    (P-level : (x : EM₁) → has-level ⟨ 1 ⟩ (P x))
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : (g₁ g₂ : G.El) →
       emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
       [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ])
    where

    f : Π EM₁ P
    f = f-aux phantom phantom where

      f-aux : Phantom emloop* → Phantom emloop-comp* → Π EM₁ P
      f-aux phantom phantom (#em₁ #embase _) = embase*

    postulate  -- HIT
      emloop-β : (g : G.El) → apd f (emloop g) == emloop* g

  open EM₁Elim public using () renaming (f to EM₁-elim)

  emloop-inv : ∀ g → emloop (G.inv g) == ! (emloop g)
  emloop-inv g = cancels-inverse _ _ lemma
    where
      cancels-inverse : ∀ {i} {A : Type i} {x y : A}
        (p : x == y) (q : y == x) → p ∙ q == idp → p == ! q
      cancels-inverse p idp r = ! (∙-unit-r p) ∙ r

      lemma : emloop (G.inv g) ∙ emloop g  == idp
      lemma = ! (emloop-comp (G.inv g) g) ∙ ap emloop (G.inv-l g) ∙ emloop-ident

  module π₁ where

    comp-equiv : ∀ g → G.El ≃ G.El
    comp-equiv g = equiv
      (λ x → G.comp x g)
      (λ x → G.comp x (G.inv g))
      (λ x → G.assoc x (G.inv g) g ∙ ap (G.comp x) (G.inv-l g) ∙ G.unit-r x)
      (λ x → G.assoc x g (G.inv g) ∙ ap (G.comp x) (G.inv-r g) ∙ G.unit-r x)

    comp-equiv-id : comp-equiv G.ident == ide G.El
    comp-equiv-id =
      pair= (λ= G.unit-r)
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop $ idf G.El))

    comp-equiv-comp : (g₁ g₂ : G.El) → comp-equiv (G.comp g₁ g₂)
                      == (comp-equiv g₂ ∘e comp-equiv g₁)
    comp-equiv-comp g₁ g₂ =
      pair= (λ= (λ x → ! (G.assoc x g₁ g₂)))
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop _))

    Ω-group : Group (lsucc i)
    Ω-group = Ω^S-group 0
      ((0 -Type i) , (G.El , G.El-level)) (0 -Type-level i)

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

    Codes : EM₁ → 0 -Type i
    Codes = EM₁-rec {C = 0 -Type i} (0 -Type-level i)
                    (G.El , G.El-level)
                    Codes-hom

    abstract
      ↓-Codes-loop : ∀ g g' → g' == G.comp g' g [ fst ∘ Codes ↓ emloop g ]
      ↓-Codes-loop g g' =
        ↓-ap-out fst Codes (emloop g) $
        ↓-ap-out (idf _) fst (ap Codes (emloop g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ ap fst w ])
                  (! (EM₁Rec.emloop-β (0 -Type-level i)
                                     (G.El , G.El-level) Codes-hom g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ w ])
                  (! (fst=-β (ua $ comp-equiv g) _)) $
        ↓-idf-ua-in (comp-equiv g) idp


    encode : {x : EM₁} → embase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α G.ident

    encode-emloop : ∀ g → encode (emloop g) == g
    encode-emloop g = to-transp $
      transport (λ x → G.ident == x [ fst ∘ Codes ↓ emloop g ])
                 (G.unit-l g) (↓-Codes-loop g G.ident)

    decode : {x : EM₁} → fst (Codes x) → embase == x
    decode {x} =
      EM₁-elim {P = λ x' → fst (Codes x') → embase == x'}
        (λ _ → Π-level (λ _ → =-preserves-level _ emlevel))
        emloop
        loop'
        (λ _ _ → prop-has-all-paths-↓ (↓-level (Π-level (λ _ → emlevel _ _))))
        x
      where
      loop' : (g : G.El)
        → emloop == emloop [ (λ x' → fst (Codes x') → embase == x') ↓ emloop g ]
      loop' g = ↓-→-from-transp $ λ= $ λ y →
        transport (λ z → embase == z) (emloop g) (emloop y)
          =⟨ trans-pathfrom (emloop g) (emloop y) ⟩
        emloop y ∙ emloop g
          =⟨ ! (emloop-comp y g) ⟩
        emloop (G.comp y g)
          =⟨ ap emloop (! (to-transp (↓-Codes-loop g y))) ⟩
        emloop (transport (λ z → fst (Codes z)) (emloop g) y) =∎

    decode-encode : ∀ {x} (α : embase == x) → decode (encode α) == α
    decode-encode idp = emloop-ident

    abstract
      Ω¹-equiv : (embase == embase) ≃ G.El
      Ω¹-equiv = equiv encode emloop encode-emloop decode-encode

    abstract
      Ω¹-path : (embase == embase) == G.El
      Ω¹-path = ua Ω¹-equiv

    abstract
      π₁-path : Trunc 0 (embase == embase) == G.El
      π₁-path = ap (Trunc 0) Ω¹-path ∙ ua (unTrunc-equiv G.El G.El-level)

    abstract
      π₁-iso : πS 0 (EM₁ , embase) ≃ᴳ G
      π₁-iso =
        (record { f = [_] ∘ emloop;
                  pres-comp = λ g₁ g₂ → ap [_] (emloop-comp g₁ g₂) } ,
         snd ((unTrunc-equiv (embase == embase) (emlevel _ _))⁻¹
              ∘e (Ω¹-equiv ⁻¹))) ⁻¹ᴳ

  {- EM₁ is 0-connected -}
  abstract
    EM₁-conn : is-connected 0 EM₁
    EM₁-conn = ([ embase ] , Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
      (EM₁-elim
        {P = λ x → [ embase ] == [ x ]}
        (λ _ → raise-level _ (=-preserves-level _ Trunc-level))
        idp
        (λ _ → prop-has-all-paths-↓ (Trunc-level {n = 0} _ _))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ Trunc-level))))
