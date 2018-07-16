{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.NConnected
open import lib.types.Truncation
open import lib.types.Group

module lib.types.EilenbergMacLane1.Core {i} where

module _ (G : Group i) where
  private
    module G = Group G

  postulate  -- HIT
    EM₁ : Type i
    embase' : EM₁
    emloop' : G.El → embase' == embase'
    emloop-comp' : ∀ g₁ g₂ → emloop' (G.comp g₁ g₂) == emloop' g₁ ∙ emloop' g₂

  emloop-coh₁' : (g₁ g₂ g₃ : G.El)
    → emloop' (G.comp (G.comp g₁ g₂) g₃) =-= emloop' g₁ ∙ (emloop' g₂ ∙ emloop' g₃)
  emloop-coh₁' g₁ g₂ g₃ =
    emloop' (G.comp (G.comp g₁ g₂) g₃)
      =⟪ emloop-comp' (G.comp g₁ g₂) g₃ ⟫
    emloop' (G.comp g₁ g₂) ∙ emloop' g₃
      =⟪ ap (λ l → l ∙ emloop' g₃) (emloop-comp' g₁ g₂) ⟫
    (emloop' g₁ ∙ emloop' g₂) ∙ emloop' g₃
      =⟪ ∙-assoc (emloop' g₁) (emloop' g₂) (emloop' g₃) ⟫
    emloop' g₁ ∙ (emloop' g₂ ∙ emloop' g₃) ∎∎

  emloop-coh₂' : (g₁ g₂ g₃ : G.El)
    → emloop' (G.comp (G.comp g₁ g₂) g₃) =-= emloop' g₁ ∙ (emloop' g₂ ∙ emloop' g₃)
  emloop-coh₂' g₁ g₂ g₃ =
    emloop' (G.comp (G.comp g₁ g₂) g₃)
      =⟪ ap emloop' (Group.assoc G g₁ g₂ g₃) ⟫
    emloop' (G.comp g₁ (G.comp g₂ g₃))
      =⟪ emloop-comp' g₁ (Group.comp G g₂ g₃) ⟫
    emloop' g₁ ∙ emloop' (G.comp g₂ g₃)
      =⟪ ap (λ l → emloop' g₁ ∙ l) (emloop-comp' g₂ g₃) ⟫
    emloop' g₁ ∙ (emloop' g₂ ∙ emloop' g₃) ∎∎

  postulate
    emloop-coh' : ∀ g₁ g₂ g₃ → emloop-coh₁' g₁ g₂ g₃ =ₛ emloop-coh₂' g₁ g₂ g₃
    EM₁-level' : has-level 2 EM₁

  ⊙EM₁ : Ptd i
  ⊙EM₁ = ⊙[ EM₁ , embase' ]

module _ {G : Group i} where
  private
    module G = Group G

  embase = embase' G
  emloop = emloop' G
  emloop-comp = emloop-comp' G
  emloop-coh₁ = emloop-coh₁' G
  emloop-coh₂ = emloop-coh₂' G
  emloop-coh = emloop-coh' G

  instance
    EM₁-level : {n : ℕ₋₂} → has-level (S (S (S (S n)))) (EM₁ G)
    EM₁-level {⟨-2⟩} = EM₁-level' G
    EM₁-level  {S n} = raise-level _ EM₁-level

  abstract
    -- This was in the original paper, but is actually derivable.
    emloop-ident : emloop G.ident == idp
    emloop-ident = ! $ anti-whisker-right (emloop G.ident) $
      ap emloop (! $ G.unit-r G.ident) ∙ emloop-comp G.ident G.ident

  module EM₁Elim {j} {P : EM₁ G → Type j}
    {{_ : (x : EM₁ G) → has-level 2 (P x)}}
    (embase* : P embase)
    (emloop* : ∀ g → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : ∀ g₁ g₂ →
       emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
       [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ])
    (emloop-coh* : ∀ g₁ g₂ g₃ →
      emloop-comp* (G.comp g₁ g₂) g₃ ∙ᵈ
      (emloop-comp* g₁ g₂ ∙ᵈᵣ emloop* g₃) ∙ᵈ
      ∙ᵈ-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃)
      ==
      ↓-ap-in (λ p → embase* == embase* [ P ↓ p ]) emloop (apd emloop* (G.assoc g₁ g₂ g₃)) ∙ᵈ
      emloop-comp* g₁ (G.comp g₂ g₃) ∙ᵈ
      (emloop* g₁ ∙ᵈₗ emloop-comp* g₂ g₃)
      [ (λ e → emloop* (G.comp (G.comp g₁ g₂) g₃) == emloop* g₁ ∙ᵈ (emloop* g₂ ∙ᵈ emloop* g₃)
               [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e ])
        ↓ =ₛ-out (emloop-coh g₁ g₂ g₃) ])
    where

    postulate  -- HIT
      f : Π (EM₁ G) P
      embase-β : f embase ↦ embase*
    {-# REWRITE embase-β #-}

    postulate  -- HIT
      emloop-β : (g : G.El) → apd f (emloop g) == emloop* g
      emloop-comp-path : (g₁ g₂ : G.El)
        → apd (apd f) (emloop-comp g₁ g₂) ▹
          apd-∙ f (emloop g₁) (emloop g₂) ∙
          ap2 _∙ᵈ_ (emloop-β g₁) (emloop-β g₂)
          ==
          emloop-β (G.comp g₁ g₂) ◃
          emloop-comp* g₁ g₂

  open EM₁Elim public using () renaming (f to EM₁-elim)

  module EM₁Level₁Elim {j} {P : EM₁ G → Type j}
    {{is-1-type : (x : EM₁ G) → has-level 1 (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : (g₁ g₂ : G.El) →
      emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
      [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ]) where

    private
      module M = EM₁Elim {{λ x → raise-level 1 (is-1-type x)}}
                         embase* emloop* emloop-comp*
                         (λ g₁ g₂ g₃ → prop-has-all-paths-↓ {{↓-level (↓-level (is-1-type embase))}})
    abstract
      f : Π (EM₁ G) P
      f = M.f

      embase-β : f embase ↦ embase*
      embase-β = M.embase-β
      {-# REWRITE embase-β #-}

      emloop-β : (g : G.El) → apd f (emloop g) == emloop* g
      emloop-β = M.emloop-β

  open EM₁Level₁Elim public using () renaming (f to EM₁-level₁-elim)

  module EM₁SetElim {j} {P : EM₁ G → Type j}
    {{is-set : (x : EM₁ G) → is-set (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ]) where

    private
      module M = EM₁Level₁Elim {P = P} {{λ x → raise-level 0 (is-set x)}}
                               embase* emloop*
                               (λ g₁ g₂ → set-↓-has-all-paths-↓ {{is-set embase}})
    open M public

  open EM₁SetElim public using () renaming (f to EM₁-set-elim)

  module EM₁PropElim {j} {P : EM₁ G → Type j}
    {{is-prop : (x : EM₁ G) → is-prop (P x)}}
    (embase* : P embase) where

    module P = EM₁SetElim {{λ x → raise-level -1 (is-prop x)}}
                          embase*
                          (λ g → prop-has-all-paths-↓ {{is-prop embase}})
    open P public

  open EM₁PropElim public using () renaming (f to EM₁-prop-elim)

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
    instance
      EM₁-conn : is-connected 0 (EM₁ G)
      EM₁-conn = has-level-in ([ embase ] , Trunc-elim
        (EM₁-level₁-elim
          {P = λ x → [ embase ] == [ x ]}
          {{λ _ → raise-level _ (=-preserves-level Trunc-level)}}
          idp
          (λ _ → prop-has-all-paths-↓)
          (λ _ _ → set-↓-has-all-paths-↓)))
