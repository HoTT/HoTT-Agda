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
open import lib.types.LoopSpace
open import lib.groups.Homomorphisms
open import lib.groups.HomotopyGroup

module lib.types.KG1 where

module KG1 {i} (G : Group i) where

  module G = Group G

  private
    data #KG1-aux : Type i where
      #kbase : #KG1-aux

    data #KG1 : Type i where
      #kg1 : #KG1-aux → (Unit → Unit) → #KG1

  KG1 : Type i
  KG1 = #KG1

  kbase : KG1
  kbase = #kg1 #kbase _

  ⊙KG1 : Ptd i
  ⊙KG1 = ⊙[ KG1 , kbase ]

  postulate  -- HIT
    klevel : has-level ⟨ 1 ⟩ KG1
    kloop : G.El → kbase == kbase
    kloop-ident : kloop G.ident == idp
    kloop-comp : ∀ g₁ g₂ → kloop (G.comp g₁ g₂) == kloop g₁ ∙ kloop g₂

  module KG1Rec {j} {C : Type j}
    (C-level : has-level ⟨ 1 ⟩ C)
    (kbase* : C)
    (hom* : GroupHom G (Ω^-Group 1 (ℕ-S≠O _) (C , kbase*) C-level)) where

    f : KG1 → C
    f (#kg1 #kbase _) = kbase*

    postulate  -- HIT
      kloop-β : (g : G.El) → ap f (kloop g) == GroupHom.f hom* g

  open KG1Rec public using () renaming (f to KG1-rec)

  module KG1Elim {j} {P : KG1 → Type j}
    (P-level : (x : KG1) → has-level ⟨ 1 ⟩ (P x))
    (kbase* : P kbase)
    (kloop* : (g : G.El) → kbase* == kbase* [ P ↓ kloop g ])
    (preserves-ident : kloop* G.ident == idp
       [ (λ p → kbase* == kbase* [ P ↓ p ]) ↓ kloop-ident ])
    (preserves-comp : (g₁ g₂ : G.El) →
       kloop* (G.comp g₁ g₂) == kloop* g₁ ∙ᵈ kloop* g₂
       [ (λ p → kbase* == kbase* [ P ↓ p ]) ↓ kloop-comp g₁ g₂ ])
    where

    f : Π KG1 P
    f (#kg1 #kbase _) = kbase*

    postulate  -- HIT
      kloop-β : (g : G.El) → apd f (kloop g) == kloop* g

  open KG1Elim public using () renaming (f to KG1-elim)

  kloop-inv : ∀ g → kloop (G.inv g) == ! (kloop g)
  kloop-inv g = cancels-inverse _ _ lemma
    where
      cancels-inverse : ∀ {i} {A : Type i} {x y : A}
        (p : x == y) (q : y == x) → p ∙ q == idp → p == ! q
      cancels-inverse p idp r = ! (∙-unit-r p) ∙ r

      lemma : kloop (G.inv g) ∙ kloop g  == idp
      lemma = ! (kloop-comp (G.inv g) g) ∙ ap kloop (G.invl g) ∙ kloop-ident

  module π₁ where

    comp-equiv : ∀ g → G.El ≃ G.El
    comp-equiv g = equiv
      (λ x → G.comp x g)
      (λ x → G.comp x (G.inv g))
      (λ x → G.assoc x (G.inv g) g ∙ ap (G.comp x) (G.invl g) ∙ G.unitr x)
      (λ x → G.assoc x g (G.inv g) ∙ ap (G.comp x) (G.invr g) ∙ G.unitr x)

    comp-equiv-id : comp-equiv G.ident == ide G.El
    comp-equiv-id =
      pair= (λ= G.unitr)
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop $ idf G.El))

    comp-equiv-comp : (g₁ g₂ : G.El) → comp-equiv (G.comp g₁ g₂)
                      == (comp-equiv g₂ ∘e comp-equiv g₁)
    comp-equiv-comp g₁ g₂ =
      pair= (λ= (λ x → ! (G.assoc x g₁ g₂)))
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop _))

    Ω-Group : Group (lsucc i)
    Ω-Group = group (G.El == G.El) (universe-=-level G.El-level G.El-level)
                    (Ω^-group-structure 1 (ℕ-S≠O _) (Type i , G.El))

    0-Group : Group (lsucc i)
    0-Group = Ω^-Group 1 (ℕ-S≠O _)
      ((⟨0⟩ -Type i) , (G.El , G.El-level)) (⟨0⟩ -Type-level i)

    Codes-hom₁ : GroupHom G Ω-Group
    Codes-hom₁ = record {
      f = ua ∘ comp-equiv;

      pres-comp = λ g₁ g₂ →
        ua (comp-equiv (G.comp g₁ g₂))
          =⟨ ap ua (comp-equiv-comp g₁ g₂) ⟩
        ua (comp-equiv g₂ ∘e comp-equiv g₁)
          =⟨ ua-∘e (comp-equiv g₁) (comp-equiv g₂) ⟩
        ua (comp-equiv g₁) ∙ ua (comp-equiv g₂) ∎}

    Codes-hom₂ : GroupHom Ω-Group 0-Group
    Codes-hom₂ = record {
      f = λ p → pair= p phap;

      pres-comp = λ p₁ p₂ →
        pair= (p₁ ∙ p₂) phap
          =⟨ prop-has-all-paths (↓-level (λ _ →
                                   raise-level _ has-level-is-prop)) _ _
              |in-ctx (λ w → pair= (p₁ ∙ p₂)  w) ⟩
        pair= (p₁ ∙ p₂) (phap {p₁} ∙ᵈ phap {p₂})
          =⟨ ! (Σ-∙ (phap {p₁}) (phap {p₂})) ⟩
        pair= p₁ phap ∙ pair= p₂ phap ∎}

      where
      -- saving some space
      phap : {p : G.El == G.El}
        → G.El-level == G.El-level [ has-level ⟨0⟩ ↓ p ]
      phap = prop-has-all-paths-↓ has-level-is-prop

    Codes-hom : GroupHom G 0-Group
    Codes-hom = Codes-hom₂ ∘hom Codes-hom₁

    Codes : KG1 → ⟨0⟩ -Type i
    Codes = KG1-rec {C = ⟨0⟩ -Type i} (⟨0⟩ -Type-level i)
                    (G.El , G.El-level)
                    Codes-hom

    abstract
      ↓-Codes-loop : ∀ g g' → g' == G.comp g' g [ fst ∘ Codes ↓ kloop g ]
      ↓-Codes-loop g g' =
        ↓-ap-out fst Codes (kloop g) $
        ↓-ap-out (idf _) fst (ap Codes (kloop g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ ap fst w ])
                  (! (KG1Rec.kloop-β (⟨0⟩ -Type-level i)
                                     (G.El , G.El-level) Codes-hom g)) $
        transport (λ w → g' == G.comp g' g [ idf _ ↓ w ])
                  (! (fst=-β (ua $ comp-equiv g) _)) $
        ↓-idf-ua-in (comp-equiv g) idp


    encode : {x : KG1} → kbase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α G.ident

    encode-kloop : ∀ g → encode (kloop g) == g
    encode-kloop g = to-transp $
      transport (λ x → G.ident == x [ fst ∘ Codes ↓ kloop g ])
                 (G.unitl g) (↓-Codes-loop g G.ident)

    decode : {x : KG1} → fst (Codes x) → kbase == x
    decode {x} =
      KG1-elim {P = λ x' → fst (Codes x') → kbase == x'}
        (λ _ → Π-level (λ _ → =-preserves-level _ klevel))
        kloop
        loop'
        (prop-has-all-paths-↓ (Π-level (λ _ → klevel _ _) _ _))
        (λ _ _ → prop-has-all-paths-↓ (↓-level (λ _ → Π-level (λ _ → klevel _ _))))
        x
      where
      loop' : (g : G.El)
        → kloop == kloop [ (λ x' → fst (Codes x') → kbase == x') ↓ kloop g ]
      loop' g = ↓-→-from-transp $ λ= $ λ y →
        transport (λ z → kbase == z) (kloop g) (kloop y)
          =⟨ trans-pathfrom (kloop g) (kloop y) ⟩
        kloop y ∙ kloop g
          =⟨ ! (kloop-comp y g) ⟩
        kloop (G.comp y g)
          =⟨ ap kloop (! (to-transp (↓-Codes-loop g y))) ⟩
        kloop (transport (λ z → fst (Codes z)) (kloop g) y) ∎

    decode-encode : ∀ {x} (α : kbase == x) → decode (encode α) == α
    decode-encode idp = kloop-ident

    abstract
      Ω¹-equiv : (kbase == kbase) ≃ G.El
      Ω¹-equiv = equiv encode kloop encode-kloop decode-encode

    abstract
      Ω¹-path : (kbase == kbase) == G.El
      Ω¹-path = ua Ω¹-equiv

    abstract
      π₁-path : Trunc ⟨0⟩ (kbase == kbase) == G.El
      π₁-path = ap (Trunc ⟨0⟩) Ω¹-path ∙ ua (unTrunc-equiv G.El G.El-level)

    abstract
      π₁-iso : π 1 (ℕ-S≠O _) (KG1 , kbase) == G
      π₁-iso = transport (λ pi → pi 1 (ℕ-S≠O _) ⊙KG1 == G) π-fold $ ! $
        group-iso
        (record { f = [_] ∘ kloop;
                  pres-comp = λ g₁ g₂ → ap [_] (kloop-comp g₁ g₂) })
        (snd ((unTrunc-equiv (kbase == kbase) (klevel _ _))⁻¹ ∘e (Ω¹-equiv ⁻¹)))

  {- KG1 is 0-connected -}
  abstract
    KG1-conn : is-connected ⟨0⟩ KG1
    KG1-conn = ([ kbase ] , Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
      (KG1-elim
        {P = λ x → [ kbase ] == [ x ]}
        (λ _ → raise-level _ (=-preserves-level _ Trunc-level))
        idp
        (λ _ → prop-has-all-paths-↓ (Trunc-level {n = ⟨0⟩} _ _))
        (set-↓-has-all-paths-↓ (=-preserves-level _ Trunc-level))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ Trunc-level))))
