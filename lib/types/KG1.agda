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
open import lib.groups.HomotopyGroup

module lib.types.KG1 where

module KG1 {i} (G : Group i) where

  open Group G

  private
    data #KG1-aux : Type i where
      #kbase : #KG1-aux

    data #KG1 : Type i where
      #kg1 : #KG1-aux → (Unit → Unit) → #KG1

  KG1 : Type i
  KG1 = #KG1

  kbase : KG1
  kbase = #kg1 #kbase _

  Ptd-KG1 : Ptd i
  Ptd-KG1 = ∙[ KG1 , kbase ]

  postulate  -- HIT
    klevel : has-level ⟨ 1 ⟩ KG1
    kloop : El → kbase == kbase
    kloop-ident : kloop ident == idp
    kloop-comp : ∀ g₁ g₂ → kloop (comp g₁ g₂) == kloop g₁ ∙ kloop g₂

  module KG1Rec {j} {C : Type j}
    (C-level : has-level ⟨ 1 ⟩ C)
    (kbase* : C) 
    (hom* : GroupHom G (Ω^-Group 1 (C , kbase*) C-level)) where

    f : KG1 → C
    f (#kg1 #kbase _) = kbase*

    postulate  -- HIT
      kloop-β : (g : El) → ap f (kloop g) == GroupHom.f hom* g

  open KG1Rec public using () renaming (f to KG1-rec)

  module KG1Elim {j} {P : KG1 → Type j}
    (P-level : (x : KG1) → has-level ⟨ 1 ⟩ (P x))
    (kbase* : P kbase)
    (kloop* : (g : El) → kbase* == kbase* [ P ↓ kloop g ])
    (preserves-ident : kloop* ident == idp
       [ (λ p → kbase* == kbase* [ P ↓ p ]) ↓ kloop-ident ])
    (preserves-comp : (g₁ g₂ : El) → 
       kloop* (comp g₁ g₂) == kloop* g₁ ∙ᵈ kloop* g₂
       [ (λ p → kbase* == kbase* [ P ↓ p ]) ↓ kloop-comp g₁ g₂ ])
    where

    f : Π KG1 P
    f (#kg1 #kbase _) = kbase*

    postulate  -- HIT
      kloop-β : (g : El) → apd f (kloop g) == kloop* g

  open KG1Elim public using () renaming (f to KG1-elim)

  kloop-inv : ∀ g → kloop (inv g) == ! (kloop g)
  kloop-inv g = cancels-inverse _ _ lemma
    where 
      cancels-inverse : ∀ {i} {A : Type i} {x y : A} 
        (p : x == y) (q : y == x) → p ∙ q == idp → p == ! q
      cancels-inverse p idp r = ! (∙-unit-r p) ∙ r

      lemma : kloop (inv g) ∙ kloop g  == idp
      lemma = ! (kloop-comp (inv g) g) ∙ ap kloop (invl g) ∙ kloop-ident

  module π₁ where

    comp-equiv : ∀ g → El ≃ El
    comp-equiv g = equiv (λ x → comp x g)
                     (λ x → comp x (inv g))
                     (λ x → assoc x (inv g) g ∙ ap (comp x) (invl g) ∙ unitr x)
                     (λ x → assoc x g (inv g) ∙ ap (comp x) (invr g) ∙ unitr x)

    comp-equiv-id : comp-equiv ident == ide El
    comp-equiv-id = 
      pair= (λ= unitr) 
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop $ idf El))

    comp-equiv-comp : (g₁ g₂ : El) → comp-equiv (comp g₁ g₂)
                      == (comp-equiv g₂ ∘e comp-equiv g₁)
    comp-equiv-comp g₁ g₂ = 
      pair= (λ= (λ x → ! (assoc x g₁ g₂)))
            (prop-has-all-paths-↓ {B = is-equiv} (is-equiv-is-prop _)) 

    Ω-Group : Group (lsucc i)
    Ω-Group = group (El == El) (universe-=-level El-level El-level)
                     (Ω^-group-structure 1 (Type i , El))

    0-Group : Group (lsucc i)
    0-Group = Ω^-Group 1 ((⟨0⟩ -Type i) , (El , El-level)) (⟨0⟩ -Type-level i)

    Codes-hom₁ : GroupHom G Ω-Group
    Codes-hom₁ = record {f = f; pres-ident = pri; pres-comp = prc}
      where
      f : El → El == El
      f = ua ∘ comp-equiv

      pri : f ident == idp
      pri = ap ua comp-equiv-id ∙ ua-η idp

      prc : (g₁ g₂ : El) → f (comp g₁ g₂) == f g₁ ∙ f g₂
      prc g₁ g₂ =
        ua (comp-equiv (comp g₁ g₂))
          =⟨ ap ua (comp-equiv-comp g₁ g₂) ⟩
        ua (comp-equiv g₂ ∘e comp-equiv g₁)
          =⟨ ua-∘e (comp-equiv g₁) (comp-equiv g₂) ⟩
        ua (comp-equiv g₁) ∙ ua (comp-equiv g₂) ∎

    Codes-hom₂ : GroupHom Ω-Group 0-Group
    Codes-hom₂ = record {f = f; pres-ident = pri; pres-comp = prc}
      where
      -- saving some space
      phap : {p : El == El}
        → El-level == El-level [ has-level ⟨0⟩ ↓ p ]
      phap = prop-has-all-paths-↓ has-level-is-prop

      f : El == El → (El , El-level) == (El , El-level)
      f p = pair= p phap
      
      pri : f idp == idp
      pri = ap (pair= idp) (contr-has-all-paths (has-level-is-prop _ _) _ _)

      prc : (p₁ p₂ : El == El) → f (p₁ ∙ p₂) == f p₁ ∙ f p₂
      prc p₁ p₂ = 
        pair= (p₁ ∙ p₂) phap
          =⟨ prop-has-all-paths (↓-level (λ _ → 
                                   raise-level _ has-level-is-prop)) _ _
              |in-ctx (λ w → pair= (p₁ ∙ p₂)  w) ⟩
        pair= (p₁ ∙ p₂) (phap {p₁} ∙ᵈ phap {p₂})
          =⟨ ! (Σ-∙ (phap {p₁}) (phap {p₂})) ⟩
        f p₁ ∙ f p₂ ∎

    Codes-hom : GroupHom G 0-Group
    Codes-hom = Codes-hom₂ ∘hom Codes-hom₁

    Codes : KG1 → ⟨0⟩ -Type i 
    Codes = KG1-rec {C = ⟨0⟩ -Type i} (⟨0⟩ -Type-level i)
                    (El , El-level)
                    Codes-hom

    abstract
      ↓-Codes-loop : ∀ g g' → g' == comp g' g [ fst ∘ Codes ↓ kloop g ]
      ↓-Codes-loop g g' = 
        ↓-ap-out fst Codes (kloop g) $
        ↓-ap-out (idf _) fst (ap Codes (kloop g)) $ 
        transport (λ w → g' == comp g' g [ idf _ ↓ ap fst w ])
                  (! (KG1Rec.kloop-β (⟨0⟩ -Type-level i)
                                     (El , El-level) Codes-hom g)) $
        transport (λ w → g' == comp g' g [ idf _ ↓ w ])
                  (! (fst=-β (ua $ comp-equiv g) _)) $
        ↓-idf-ua-in (comp-equiv g) idp

    
    decode' : El → kbase == kbase
    decode' = kloop

    encode : {x : KG1} → kbase == x → fst (Codes x)
    encode α = transport (fst ∘ Codes) α ident

    encode-decode' : ∀ g → encode (decode' g) == g
    encode-decode' g = to-transp $
      transport (λ x → ident == x [ fst ∘ Codes ↓ kloop g ])
                 (unitl g) (↓-Codes-loop g ident)

    decode : {x : KG1} → fst (Codes x) → kbase == x
    decode {x} = 
      KG1-elim {P = λ x' → fst (Codes x') → kbase == x'}
        (λ _ → Π-level (λ _ → =-preserves-level _ klevel))
        decode'
        loop'
        (prop-has-all-paths-↓ (Π-level (λ _ → klevel _ _) _ _))
        (λ _ _ → prop-has-all-paths-↓ (↓-level (λ _ → Π-level (λ _ → klevel _ _))))
        x
      where 
      loop' : (g : El) 
        → decode' == decode' [ (λ x' → fst (Codes x') → kbase == x') ↓ kloop g ]
      loop' g = ↓-→-from-transp $ λ= $ λ y →
        transport (λ z → kbase == z) (kloop g) (kloop y)
          =⟨ trans-pathfrom (kloop g) (kloop y) ⟩
        kloop y ∙ kloop g
          =⟨ ! (kloop-comp y g) ⟩
        kloop (comp y g)
          =⟨ ap kloop (! (to-transp (↓-Codes-loop g y))) ⟩
        kloop (transport (λ z → fst (Codes z)) (kloop g) y) ∎

    decode-encode : ∀ {x} (α : kbase == x) → decode (encode α) == α
    decode-encode α = 
      J (λ (x : KG1) (α : kbase == x) → decode (encode α) == α) kloop-ident α

    abstract
      Ω¹-equiv : (kbase == kbase) ≃ El
      Ω¹-equiv = equiv encode decode' encode-decode' decode-encode

    abstract
      Ω¹-path : (kbase == kbase) == El
      Ω¹-path = ua Ω¹-equiv

    abstract
      π₁-path : Trunc ⟨0⟩ (kbase == kbase) == El
      π₁-path = ap (Trunc ⟨0⟩) Ω¹-path ∙ ua (unTrunc-equiv El El-level)
    
    abstract
      π₁-iso : ⦃ p1 : 1 ≠ 0 ⦄ → π 1 ⦃ p1 ⦄ (KG1 , kbase) == G
      π₁-iso ⦃ p1 ⦄ = transport (λ pi → pi 1 ⦃ p1 ⦄ Ptd-KG1 == G) π-fold $ ! $
        group-iso 
        (record { f = [_] ∘ decode';
                  pres-ident = ap [_] kloop-ident; 
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
