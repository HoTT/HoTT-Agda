{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2
open import lib.NConnected
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Group
open import lib.groups.LoopSpace
open import lib.groups.Homomorphism

module lib.types.EilenbergMacLane1 {i} where

module _ where
  private
    data #EM₁-aux (G : Group i) : Type i where
      #embase : #EM₁-aux G

    data #EM₁ (G : Group i) : Type i where
      #em₁ : #EM₁-aux G → (Unit → Unit) → #EM₁ G

  module _ (G : Group i) where

    EM₁ : Type i
    EM₁ = #EM₁ G

    embase' : EM₁
    embase' = #em₁ #embase _

    ⊙EM₁ : Ptd i
    ⊙EM₁ = ⊙[ EM₁ , embase' ]

    postulate  -- HIT
      emloop' : Group.El G → embase'  == embase'
      emloop-comp' : ∀ g₁ g₂ → emloop' (Group.comp G g₁ g₂) == emloop' g₁ ∙ emloop' g₂
      EM₁-level' : has-level ⟨ 1 ⟩ EM₁

  module _ {G : Group i} where
    private
      module G = Group G

    embase = embase' G
    emloop = emloop' G
    emloop-comp = emloop-comp' G
    EM₁-level = EM₁-level' G

    abstract
      -- This was in the original paper, but is actually derivable.
      emloop-ident : emloop G.ident == idp
      emloop-ident = ! $ anti-whisker-right (emloop G.ident) $
        ap emloop (! $ G.unit-r G.ident) ∙ emloop-comp G.ident G.ident

    module EM₁Rec {j} {C : Type j}
      (C-level : has-level ⟨ 1 ⟩ C)
      (embase* : C)
      (hom* : G →ᴳ (Ω^S-group 0 (C , embase*) C-level)) where

      -- FIXME Should be defined from the dependent one.
      f : EM₁ G → C
      f = f-aux phantom  where

        f-aux : Phantom hom* → (EM₁ G → C)
        f-aux phantom (#em₁ #embase _) = embase*

      postulate  -- HIT
        emloop-β : (g : G.El) → ap f (emloop g) == GroupHom.f hom* g

    open EM₁Rec public using () renaming (f to EM₁-rec)

    module EM₁Elim {j} {P : EM₁ G → Type j}
      (P-level : (x : EM₁ G) → has-level ⟨ 1 ⟩ (P x))
      (embase* : P embase)
      (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
      (emloop-comp* : (g₁ g₂ : G.El) →
         emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
         [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ])
      where

      f : Π (EM₁ G) P
      f = f-aux phantom phantom where

        f-aux : Phantom emloop* → Phantom emloop-comp* → Π (EM₁ G) P
        f-aux phantom phantom (#em₁ #embase _) = embase*

      postulate  -- HIT
        emloop-β : (g : G.El) → apd f (emloop g) == emloop* g

    open EM₁Elim public using () renaming (f to EM₁-elim)

-- basic lemmas about [EM₁]

module _ {G : Group i} where
  private
    module G = Group G

  abstract
    emloop-inv : ∀ g → emloop' G (G.inv g) == ! (emloop g)
    emloop-inv g = cancels-inverse _ _ lemma
      where
        cancels-inverse : ∀ {i} {A : Type i} {x y : A}
          (p : x == y) (q : y == x) → p ∙ q == idp → p == ! q
        cancels-inverse p idp r = ! (∙-unit-r p) ∙ r

        lemma : emloop' G (G.inv g) ∙ emloop g  == idp
        lemma = ! (emloop-comp (G.inv g) g) ∙ ap emloop (G.inv-l g) ∙ emloop-ident

    {- EM₁ is 0-connected -}
    EM₁-conn : is-connected 0 (EM₁ G)
    EM₁-conn = ([ embase ] , Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
      (EM₁-elim
        {P = λ x → [ embase ] == [ x ]}
        (λ _ → raise-level _ (=-preserves-level _ Trunc-level))
        idp
        (λ _ → prop-has-all-paths-↓ (Trunc-level {n = 0} _ _))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ Trunc-level))))
