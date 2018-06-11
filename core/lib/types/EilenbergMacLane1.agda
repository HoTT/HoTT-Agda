{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2
open import lib.NConnected
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Group
open import lib.groups.LoopSpace
open import lib.types.PathSeq
open import lib.groups.Homomorphism
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FundamentalCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.GroupToCategory

module lib.types.EilenbergMacLane1 {i} where

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
    EM₁-level' : has-level ⟨ 2 ⟩ EM₁

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
    {{_ : (x : EM₁ G) → has-level ⟨ 2 ⟩ (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : (g₁ g₂ : G.El) →
       emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
       [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ])
    (emloop-coh* : (g₁ g₂ g₃ : G.El) →
      emloop-comp* (G.comp g₁ g₂) g₃ ∙ᵈ (emloop-comp* g₁ g₂ ∙ᵈᵣ emloop* g₃) ∙ᵈ ∙ᵈ-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃)
      == ↓-ap-in (λ p → embase* == embase* [ P ↓ p ]) emloop (apd emloop* (G.assoc g₁ g₂ g₃)) ∙ᵈ emloop-comp* g₁ (G.comp g₂ g₃) ∙ᵈ (emloop* g₁ ∙ᵈₗ emloop-comp* g₂ g₃)
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
    {{is-1-type : (x : EM₁ G) → has-level ⟨ 1 ⟩ (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : (g₁ g₂ : G.El) →
      emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
      [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ]) where

    module M = EM₁Elim {{λ x → raise-level 1 (is-1-type x)}}
                       embase* emloop* emloop-comp*
                       (λ g₁ g₂ g₃ → prop-has-all-paths-↓ {{↓-level (↓-level (is-1-type embase))}})
    open M public

  open EM₁Level₁Elim public using () renaming (f to EM₁-level₁-elim)

  module EM₁SetElim {j} {P : EM₁ G → Type j}
    {{is-set : (x : EM₁ G) → is-set (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ]) where

    module N = EM₁Level₁Elim {{λ x → raise-level 0 (is-set x)}}
                             embase* emloop*
                             (λ g₁ g₂ → set-↓-has-all-paths-↓ {{is-set embase}})
    open N public

  open EM₁SetElim public using () renaming (f to EM₁-set-elim)

  module EM₁PropElim {j} {P : EM₁ G → Type j}
    {{is-prop : (x : EM₁ G) → is-prop (P x)}}
    (embase* : P embase) where

    module P = EM₁SetElim {{λ x → raise-level -1 (is-prop x)}}
                          embase*
                          (λ g → prop-has-all-paths-↓ {{is-prop embase}})
    open P public

  open EM₁PropElim public using () renaming (f to EM₁-prop-elim)

  module EM₁Rec' {j} {C : Type j}
    {{_ : has-level ⟨ 2 ⟩ C}}
    (embase* : C)
    (emloop* : (g : G.El) → embase* == embase*)
    (emloop-comp* : (g₁ g₂ : G.El) → emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ emloop* g₂)
    (emloop-coh* : (g₁ g₂ g₃ : G.El) →
      emloop-comp* (G.comp g₁ g₂) g₃ ◃∙
      ap (λ l → l ∙ emloop* g₃) (emloop-comp* g₁ g₂) ◃∙
      ∙-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃) ◃∎
      =ₛ
      ap emloop* (G.assoc g₁ g₂ g₃) ◃∙
      emloop-comp* g₁ (G.comp g₂ g₃) ◃∙
      ap (λ l → emloop* g₁ ∙ l) (emloop-comp* g₂ g₃) ◃∎) where

    private
      P : EM₁ G → Type j
      P _ = C

      emloop** : (g : G.El) → embase* == embase* [ P ↓ emloop g ]
      emloop** g = ↓-cst-in (emloop* g)

      emloop-comp** : (g₁ g₂ : G.El) → emloop** (G.comp g₁ g₂) == emloop** g₁ ∙ᵈ emloop** g₂ [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ]
      emloop-comp** g₁ g₂ = ↓-cst-in2 (emloop-comp* g₁ g₂) ▹ ↓-cst-in-∙ (emloop g₁) (emloop g₂) (emloop* g₁) (emloop* g₂)

      module _ (g₁ g₂ g₃ : G.El) where

        s₀ : embase == embase
        s₀ = emloop (G.comp (G.comp g₁ g₂) g₃)

        s₁ : embase == embase
        s₁ = emloop (G.comp g₁ g₂) ∙ emloop g₃

        s₂ : embase == embase
        s₂ = (emloop g₁ ∙ emloop g₂) ∙ emloop g₃

        s₃ : embase == embase
        s₃ = emloop g₁ ∙ (emloop g₂ ∙ emloop g₃)

        s₄ : embase == embase
        s₄ = emloop (G.comp g₁ (G.comp g₂ g₃))

        s₅ : embase == embase
        s₅ = emloop g₁ ∙ emloop (G.comp g₂ g₃)

        e₀₁ : s₀ == s₁
        e₀₁ = emloop-comp (G.comp g₁ g₂) g₃

        e₁₂ : s₁ == s₂
        e₁₂ = ap (λ l → l ∙ emloop g₃) (emloop-comp g₁ g₂)

        e₂₃ : s₂ == s₃
        e₂₃ = ∙-assoc (emloop g₁) (emloop g₂) (emloop g₃)

        e₀₄ : s₀ == s₄
        e₀₄ = ap emloop (G.assoc g₁ g₂ g₃)

        e₄₅ : s₄ == s₅
        e₄₅ = emloop-comp g₁ (G.comp g₂ g₃)

        e₅₃ : s₅ == s₃
        e₅₃ = ap (λ l → emloop g₁ ∙ l) (emloop-comp g₂ g₃)

        φ : s₀ == s₃
        φ = ↯ e₀₁ ◃∙ e₁₂ ◃∙ e₂₃ ◃∎

        ψ : s₀ == s₃
        ψ = ↯ e₀₄ ◃∙ e₄₅ ◃∙ e₅₃ ◃∎

        φ=ψ : φ == ψ
        φ=ψ = =ₛ-out (emloop-coh g₁ g₂ g₃)

        s₀* : embase* == embase*
        s₀* = emloop* (G.comp (G.comp g₁ g₂) g₃)

        s₁* : embase* == embase*
        s₁* = emloop* (G.comp g₁ g₂) ∙ emloop* g₃

        s₂* : embase* == embase*
        s₂* = (emloop* g₁ ∙ emloop* g₂) ∙ emloop* g₃

        s₃* : embase* == embase*
        s₃* = emloop* g₁ ∙ (emloop* g₂ ∙ emloop* g₃)

        s₄* : embase* == embase*
        s₄* = emloop* (G.comp g₁ (G.comp g₂ g₃))

        s₅* : embase* == embase*
        s₅* = emloop* g₁ ∙ emloop* (G.comp g₂ g₃)

        e₀₁* : s₀* == s₁*
        e₀₁* = emloop-comp* (G.comp g₁ g₂) g₃

        e₁₂* : s₁* == s₂*
        e₁₂* = ap (λ l → l ∙ emloop* g₃) (emloop-comp* g₁ g₂)

        e₂₃* : s₂* == s₃*
        e₂₃* = ∙-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃)

        e₀₄* : s₀* == s₄*
        e₀₄* = ap emloop* (G.assoc g₁ g₂ g₃)

        e₄₅* : s₄* == s₅*
        e₄₅* = emloop-comp* g₁ (G.comp g₂ g₃)

        e₅₃* : s₅* == s₃*
        e₅₃* = ap (λ l → emloop* g₁ ∙ l) (emloop-comp* g₂ g₃)

        φ* : s₀* == s₃*
        φ* = ↯ e₀₁* ◃∙ e₁₂* ◃∙ e₂₃* ◃∎

        ψ* : s₀* == s₃*
        ψ* = ↯ e₀₄* ◃∙ e₄₅* ◃∙ e₅₃* ◃∎

        φ*=ψ* : φ* == ψ*
        φ*=ψ* = =ₛ-out (emloop-coh* g₁ g₂ g₃)

        s₀** : embase* == embase* [ P ↓ s₀ ]
        s₀** = emloop** (G.comp (G.comp g₁ g₂) g₃)

        s₁** : embase* == embase* [ P ↓ s₁ ]
        s₁** = emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃

        s₂** : embase* == embase* [ P ↓ s₂ ]
        s₂** = (emloop** g₁ ∙ᵈ emloop** g₂) ∙ᵈ emloop** g₃

        s₃** : embase* == embase* [ P ↓ s₃ ]
        s₃** = emloop** g₁ ∙ᵈ (emloop** g₂ ∙ᵈ emloop** g₃)

        s₄** : embase* == embase* [ P ↓ s₄ ]
        s₄** = emloop** (G.comp g₁ (G.comp g₂ g₃))

        s₅** : embase* == embase* [ P ↓ s₅ ]
        s₅** = emloop** g₁ ∙ᵈ emloop** (G.comp g₂ g₃)

        e₀₁** : s₀** == s₁** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₀₁ ]
        e₀₁** = emloop-comp** (G.comp g₁ g₂) g₃

        e₁₂** : s₁** == s₂** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₁₂ ]
        e₁₂** = emloop-comp** g₁ g₂ ∙ᵈᵣ emloop** g₃

        e₂₃** : s₂** == s₃** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₂₃ ]
        e₂₃** = ∙ᵈ-assoc (emloop** g₁) (emloop** g₂) (emloop** g₃)

        e₀₄** : s₀** == s₄** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₀₄ ]
        e₀₄** = ↓-ap-in (λ p → embase* == embase* [ P ↓ p ]) emloop (apd emloop** (G.assoc g₁ g₂ g₃))

        e₄₅** : s₄** == s₅** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₄₅ ]
        e₄₅** = emloop-comp** g₁ (G.comp g₂ g₃)

        e₅₃** : s₅** == s₃** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ e₅₃ ]
        e₅₃** = emloop** g₁ ∙ᵈₗ emloop-comp** g₂ g₃

        φ** : s₀** == s₃** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ φ ]
        φ** = e₀₁** ∙ᵈ e₁₂** ∙ᵈ e₂₃**

        ψ** : s₀** == s₃** [ (λ s → embase* == embase* [ P ↓ s ]) ↓ ψ ]
        ψ** = e₀₄** ∙ᵈ e₄₅** ∙ᵈ e₅₃**

        tt₁ : ↓-cst-in s₃* == emloop** g₁ ∙ᵈ ↓-cst-in {p = emloop g₂ ∙ emloop g₃} (emloop* g₂ ∙ emloop* g₃)
        tt₁ = ↓-cst-in-∙ (emloop g₁) (emloop g₂ ∙ emloop g₃) (emloop* g₁) (emloop* g₂ ∙ emloop* g₃)

        tt₂' : ↓-cst-in {p = emloop g₂ ∙ emloop g₃} (emloop* g₂ ∙ emloop* g₃) == emloop** g₂ ∙ᵈ emloop** g₃
        tt₂' = ↓-cst-in-∙ (emloop g₂) (emloop g₃) (emloop* g₂) (emloop* g₃)

        tt₂ : emloop** g₁ ∙ᵈ ↓-cst-in {p = emloop g₂ ∙ emloop g₃} (emloop* g₂ ∙ emloop* g₃) == s₃**
        tt₂ = emloop** g₁ ∙ᵈₗ tt₂'

        tt : ↓-cst-in s₃* == s₃**
        tt = tt₁ ∙ tt₂

        dd : (r : s₀ == s₃) → s₀* == s₃* → s₀** == s₃** [ (λ p → embase* == embase* [ P ↓ p ]) ↓ r ]
        dd r q = ↓-cst-in2 {q = r} q ▹ tt

        cc : dd φ φ* == φ**
        cc =
          ↓-cst-in2 {q = φ} φ* ▹ tt
            =⟨ (↓-cst-in2-∙ {p₀₁ = e₀₁} {p₁₂ = e₁₂ ∙ e₂₃} e₀₁* (e₁₂* ∙ e₂₃*)) ∙'ᵈᵣ tt ⟩
          (e₀₁*' ∙ᵈ ↓-cst-in2 {q = e₁₂ ∙ e₂₃} (e₁₂* ∙ e₂₃*)) ▹ tt
            =⟨ (↓-cst-in2-∙ {p₀₁ = e₁₂} {p₁₂ = e₂₃} e₁₂* e₂₃*) |in-ctx (λ y → (e₀₁*' ∙ᵈ y) ▹ tt) ⟩
          (e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ e₂₃*') ▹ tt
            =⟨ ∙ᵈ-∙'ᵈ-assoc' e₀₁*' (e₁₂*' ∙ᵈ e₂₃*') tt ⟩
          e₀₁*' ∙ᵈ (e₁₂*' ∙ᵈ e₂₃*') ▹ tt
            =⟨ ∙ᵈ-∙'ᵈ-assoc' e₁₂*' e₂₃*' tt |in-ctx (λ y → e₀₁*' ∙ᵈ y) ⟩
          e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ e₂₃*' ▹ tt
            =⟨ ↓-cst-in-assoc {p₀ = emloop g₁} {p₁ = emloop g₂} {p₂ = emloop g₃} (emloop* g₁) (emloop* g₂) (emloop* g₃) |in-ctx (λ y → e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ y) ⟩
          e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ f₂ ◃ f₃ ◃ e₂₃**
            =⟨ ! (◃▹-assoc e₁₂*' f₂ (f₃ ◃ e₂₃**)) |in-ctx (λ y → e₀₁*' ∙ᵈ y) ⟩
          e₀₁*' ∙ᵈ (e₁₂*' ▹ f₂) ∙ᵈ f₃ ◃ e₂₃**
            =⟨ ↓-cst-in2-whisker-right {p' = emloop g₃} {q' = emloop* g₃} {p₀₁ = emloop-comp g₁ g₂} (emloop-comp* g₁ g₂) |in-ctx (λ y → e₀₁*' ∙ᵈ y ∙ᵈ f₃ ◃ e₂₃**) ⟩
          e₀₁*' ∙ᵈ (f₀ ◃ f₁) ∙ᵈ f₃ ◃ e₂₃**
            =⟨ ∙ᵈ-assoc f₀ f₁ (f₃ ◃ e₂₃**) |in-ctx (λ y → e₀₁*' ∙ᵈ y) ⟩
          e₀₁*' ∙ᵈ f₀ ◃ f₁ ∙ᵈ f₃ ◃ e₂₃**
            =⟨ ! (◃▹-assoc e₀₁*' f₀ (f₁ ∙ᵈ f₃ ◃ e₂₃**)) ⟩
          e₀₁** ∙ᵈ f₁ ∙ᵈ f₃ ◃ e₂₃**
            =⟨ ! (◃▹-assoc f₁ f₃ e₂₃**) |in-ctx (λ y → e₀₁** ∙ᵈ y) ⟩
          e₀₁** ∙ᵈ (f₁ ▹ f₃) ∙ᵈ e₂₃**
            =⟨ ! (∙ᵈᵣ-∙'ᵈ f₁' f₃' (emloop** g₃)) |in-ctx (λ y → e₀₁** ∙ᵈ y ∙ᵈ e₂₃**) ⟩
          φ** =∎
          where
          e₀₁*' : ↓-cst-in s₀* == ↓-cst-in s₁* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₀₁ ]
          e₀₁*' = ↓-cst-in2 {q = e₀₁} e₀₁*
          e₁₂*' : ↓-cst-in s₁* == ↓-cst-in s₂* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₁₂ ]
          e₁₂*' = ↓-cst-in2 {q = e₁₂} e₁₂*
          e₂₃*' : ↓-cst-in s₂* == ↓-cst-in s₃* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₂₃ ]
          e₂₃*' = ↓-cst-in2 {q = e₂₃} e₂₃*
          f₀ : ↓-cst-in (emloop* (G.comp g₁ g₂) ∙ emloop* g₃) ==
               emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃
          f₀ = ↓-cst-in-∙ (emloop (G.comp g₁ g₂)) (emloop g₃) (emloop* (G.comp g₁ g₂)) (emloop* g₃)
          f₁' : emloop** (G.comp g₁ g₂) == ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂)
                  [ (λ s → embase* == embase* [ P ↓ s ]) ↓ emloop-comp' G g₁ g₂ ]
          f₁' = ↓-cst-in2 {q = emloop-comp g₁ g₂} (emloop-comp* g₁ g₂)
          f₁ : emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃ ==
               ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃
                 [ (λ s → embase* == embase* [ P ↓ s ]) ↓ ap (λ r → r ∙ emloop' G g₃) (emloop-comp' G g₁ g₂) ]
          f₁ = f₁' ∙ᵈᵣ emloop** g₃
          f₂ : ↓-cst-in ((emloop* g₁ ∙ emloop* g₂) ∙ emloop* g₃) ==
               ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃
          f₂ = ↓-cst-in-∙ (emloop g₁ ∙ emloop g₂) (emloop g₃) (emloop* g₁ ∙ emloop* g₂) (emloop* g₃)
          f₃' : ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) == (emloop** g₁ ∙ᵈ emloop** g₂)
          f₃' = ↓-cst-in-∙ (emloop g₁) (emloop g₂) (emloop* g₁) (emloop* g₂)
          f₃ : ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃ ==
               (emloop** g₁ ∙ᵈ emloop** g₂) ∙ᵈ emloop** g₃
          f₃ = f₃' ∙ᵈᵣ emloop** g₃

        ee : dd ψ ψ* == ψ**
        ee =
          ↓-cst-in2 {q = ψ} ψ* ▹ tt
            =⟨ ↓-cst-in2-∙ {p₀₁ = e₀₄} {p₁₂ = e₄₅ ∙ e₅₃} e₀₄* (e₄₅* ∙ e₅₃*) |in-ctx (λ y → y ▹ tt) ⟩
          (e₀₄*' ∙ᵈ ↓-cst-in2 {q = e₄₅ ∙ e₅₃} (e₄₅* ∙ e₅₃*)) ▹ tt
            =⟨ ↓-cst-in2-∙ {p₀₁ = e₄₅} {p₁₂ = e₅₃} e₄₅* e₅₃* |in-ctx (λ y → (e₀₄*' ∙ᵈ y) ▹ tt) ⟩
          (e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*') ▹ tt
            =⟨ ∙ᵈ-∙'ᵈ-assoc' e₀₄*' (e₄₅*' ∙ᵈ e₅₃*') tt ⟩
          e₀₄*' ∙ᵈ (e₄₅*' ∙ᵈ e₅₃*') ▹ tt
            =⟨ ∙ᵈ-∙'ᵈ-assoc' e₄₅*' e₅₃*' tt |in-ctx (λ y → e₀₄*' ∙ᵈ y) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ tt
            =⟨ ∙=∙' tt₁ tt₂ |in-ctx (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ y) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ (tt₁ ∙' tt₂)
            =⟨ ! (∙'ᵈ-assoc e₅₃*' tt₁ tt₂) |in-ctx (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ (e₅₃*' ▹ tt₁) ▹ tt₂
            =⟨ ↓-cst-in2-whisker-left {p = emloop g₁} {q = emloop* g₁} {p₀₁' = emloop-comp g₂ g₃} (emloop-comp* g₂ g₃) |in-ctx (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y ▹ tt₂) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ (f₀ ◃ f₁) ▹ tt₂
            =⟨ ∙ᵈ-∙'ᵈ-assoc f₀ f₁ tt₂ |in-ctx (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ (f₁ ▹ tt₂)
            =⟨ ! (∙ᵈₗ-∙'ᵈ f₁' tt₂' (emloop** g₁)) |in-ctx (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ y) ⟩
          e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ e₅₃**
            =⟨ ! (◃▹-assoc e₄₅*' f₀ e₅₃**) |in-ctx (λ y → e₀₄*' ∙ᵈ y) ⟩
          e₀₄*' ∙ᵈ e₄₅** ∙ᵈ e₅₃**
            =⟨ ↓-cst-in2-ap emloop emloop* (G.assoc g₁ g₂ g₃) |in-ctx (λ y → y ∙ᵈ e₄₅** ∙ᵈ e₅₃**) ⟩
          ψ** =∎
          where
          e₀₄*' : ↓-cst-in s₀* == ↓-cst-in s₄* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₀₄ ]
          e₀₄*' = ↓-cst-in2 {q = e₀₄} e₀₄*
          e₄₅*' : ↓-cst-in s₄* == ↓-cst-in s₅* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₄₅ ]
          e₄₅*' = ↓-cst-in2 {q = e₄₅} e₄₅*
          e₅₃*' : ↓-cst-in s₅* == ↓-cst-in s₃* [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e₅₃ ]
          e₅₃*' = ↓-cst-in2 {q = e₅₃} e₅₃*
          f₀ : ↓-cst-in (emloop* g₁ ∙ emloop* (G.comp g₂ g₃)) == emloop** g₁ ∙ᵈ ↓-cst-in (emloop* (G.comp g₂ g₃))
          f₀ = ↓-cst-in-∙ (emloop g₁) (emloop' G (G.comp g₂ g₃)) (emloop* g₁) (emloop* (G.comp g₂ g₃))
          f₁' : emloop** (G.comp g₂ g₃) == ↓-cst-in (emloop* g₂ ∙ emloop* g₃)
                  [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₂ g₃ ]
          f₁' = ↓-cst-in2 {q = emloop-comp g₂ g₃} (emloop-comp* g₂ g₃)
          f₁ : emloop** g₁ ∙ᵈ emloop** (G.comp g₂ g₃) == emloop** g₁ ∙ᵈ ↓-cst-in (emloop* g₂ ∙ emloop* g₃)
                 [ (λ p → embase* == embase* [ P ↓ p ]) ↓ ap (λ y → emloop g₁ ∙ y) (emloop-comp g₂ g₃) ]
          f₁ = emloop** g₁ ∙ᵈₗ f₁'

        abstract
          emloop-coh** : φ** == ψ** [ (λ e → s₀** == s₃** [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e ]) ↓ φ=ψ ]
          emloop-coh** = (! cc) ◃ ap (λ y → dd φ y) φ*=ψ* ◃ apd (λ y → dd y ψ*) φ=ψ ▹ ee

      module M = EM₁Elim {P = λ _ → C} embase* emloop** emloop-comp** emloop-coh**

    abstract
      f : EM₁ G → C
      f = M.f

      embase-β : f embase ↦ embase*
      embase-β = M.embase-β
      {-# REWRITE embase-β #-}

      emloop-β : (g : G.El) → ap f (emloop g) == emloop* g
      emloop-β g = apd=cst-in (M.emloop-β g)

      private
        middle-fun : ∀ {i j} {A : Type i} {B : Type j}
          {f : A → B} {a₀ a₁ a₂ : A}
          (p₀₁ : a₀ == a₁) (p₁₂ : a₁ == a₂) (p₀₂ : a₀ == a₂)
          (q₀₁ : f a₀ == f a₁) (q₁₂ : f a₁ == f a₂) (q₀₂ : f a₀ == f a₂)
          (p-comp : p₀₂ == p₀₁ ∙ p₁₂)
          → apd f p₀₂ == ↓-cst-in {p = p₀₁} q₀₁ ∙ᵈ ↓-cst-in {p = p₁₂} q₁₂
              [ (λ w → f a₀ == f a₂ [ (λ _ → B) ↓ w ]) ↓ p-comp ]
          → ap f p₀₂ == q₀₁ ∙ q₁₂
        middle-fun {f = f} p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp inner =
          ap=↓-cst-out-apd f p₀₂ ∙
          ↓-cst-out2 inner ∙
          ↓-cst-out2 (! (↓-cst-in-∙ p₀₁ p₁₂ q₀₁ q₁₂)) ∙
          ↓-cst-β (p₀₁ ∙ p₁₂) (q₀₁ ∙ q₁₂)

        emloop-comp-path-rewrite₁ : ∀ {i j} {A : Type i} {B : Type j}
          {f : A → B} {a₀ a₁ a₂ : A}
          (p₀₁ : a₀ == a₁) (p₁₂ : a₁ == a₂) (p₀₂ : a₀ == a₂)
          (q₀₁ : f a₀ == f a₁) (q₁₂ : f a₁ == f a₂) (q₀₂ : f a₀ == f a₂)
          (p-comp : p₀₂ == p₀₁ ∙ p₁₂)
          (r₀₁ : apd f p₀₁ == ↓-cst-in q₀₁)
          (r₁₂ : apd f p₁₂ == ↓-cst-in q₁₂)
          → ap (ap f) p-comp ∙
            ap-∙ f p₀₁ p₁₂ ∙
            ap2 _∙_ (apd=cst-in r₀₁) (apd=cst-in r₁₂)
            ==
            middle-fun p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp
              (apd (apd f) p-comp ▹
               apd-∙ f p₀₁ p₁₂ ∙
               ap2 _∙ᵈ_ r₀₁ r₁₂)
        emloop-comp-path-rewrite₁ idp idp .idp q₀₁ q₁₂ q₀₂ idp r₀₁ r₁₂ =
          ! (∙-unit-r (idp ∙' ap2 _∙_ r₀₁ r₁₂) ∙ ∙'-unit-l (ap2 _∙_ r₀₁ r₁₂))

        emloop-comp-path-rewrite₂ : ∀ {i j} {A : Type i} {B : Type j}
          {f : A → B} {a₀ a₁ a₂ : A}
          (p₀₁ : a₀ == a₁) (p₁₂ : a₁ == a₂) (p₀₂ : a₀ == a₂)
          (q₀₁ : f a₀ == f a₁) (q₁₂ : f a₁ == f a₂) (q₀₂ : f a₀ == f a₂)
          (p-comp : p₀₂ == p₀₁ ∙ p₁₂) (q-comp : q₀₂ == q₀₁ ∙ q₁₂)
          (r₀₁ : apd f p₀₁ == ↓-cst-in q₀₁)
          (r₁₂ : apd f p₁₂ == ↓-cst-in q₁₂)
          (r₀₂ : apd f p₀₂ == ↓-cst-in q₀₂)
          → middle-fun p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp
              (r₀₂ ◃
               ↓-cst-in2 {q = p-comp} q-comp ▹
               ↓-cst-in-∙ p₀₁ p₁₂ q₀₁ q₁₂)
            ==
            apd=cst-in r₀₂ ∙
            q-comp
        emloop-comp-path-rewrite₂ idp idp .idp q₀₁ q₁₂ q₀₂ idp q-comp r₀₁ r₁₂ r₀₂ =
          ∙-unit-r (r₀₂ ∙ q-comp)

      emloop-comp-path : (g₁ g₂ : G.El)
        → ap (ap f) (emloop-comp g₁ g₂) ∙
          ap-∙ f (emloop g₁) (emloop g₂) ∙
          ap2 _∙_ (emloop-β g₁) (emloop-β g₂)
          ==
          emloop-β (G.comp g₁ g₂) ∙
          emloop-comp* g₁ g₂
      emloop-comp-path g₁ g₂ =
        ap (ap f) (emloop-comp g₁ g₂) ∙
        ap-∙ f (emloop g₁) (emloop g₂) ∙
        ap2 _∙_ (emloop-β g₁) (emloop-β g₂)
          =⟨ emloop-comp-path-rewrite₁ p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp r₀₁ r₁₂ ⟩
        fun (apd (apd f) (emloop-comp g₁ g₂) ▹
             apd-∙ f (emloop g₁) (emloop g₂) ∙
             ap2 _∙ᵈ_ (M.emloop-β g₁) (M.emloop-β g₂))
          =⟨ ap fun (M.emloop-comp-path g₁ g₂) ⟩
        fun (M.emloop-β (G.comp g₁ g₂) ◃ emloop-comp** g₁ g₂)
          =⟨ emloop-comp-path-rewrite₂ p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp q-comp r₀₁ r₁₂ r₀₂ ⟩
        emloop-β (G.comp g₁ g₂) ∙ emloop-comp* g₁ g₂ =∎
        where
          p₀₁ = emloop g₁
          p₁₂ = emloop g₂
          p₀₂ = emloop (G.comp g₁ g₂)
          q₀₁ = emloop* g₁
          q₁₂ = emloop* g₂
          q₀₂ = emloop* (G.comp g₁ g₂)
          r₀₁ = M.emloop-β g₁
          r₁₂ = M.emloop-β g₂
          r₀₂ = M.emloop-β (G.comp g₁ g₂)
          p-comp = emloop-comp g₁ g₂
          q-comp = emloop-comp* g₁ g₂
          fun = middle-fun p₀₁ p₁₂ p₀₂ q₀₁ q₁₂ q₀₂ p-comp

  module EM₁Rec {j} {C : Type j}
    {{C-level : has-level ⟨ 2 ⟩ C}}
    (F : TwoSemiFunctor (group-to-cat G) (2-type-fundamental-cat C {{C-level}})) where

    private
      module F = TwoSemiFunctor F
      module M = EM₁Rec' {C = C} {{C-level}}
                         (F.F₀ unit)
                         F.F₁
                         F.pres-comp
                         F.pres-comp-coh

    abstract
      f : EM₁ G → C
      f = M.f

      embase-β : f embase ↦ F.F₀ unit
      embase-β = M.embase-β
      {-# REWRITE embase-β #-}

      emloop-β : (g : G.El) → ap f (emloop g) == F.F₁ g
      emloop-β = M.emloop-β

      emloop-comp-path : (g₁ g₂ : G.El)
        → ap (ap f) (emloop-comp g₁ g₂) ∙
          ap-∙ f (emloop g₁) (emloop g₂) ∙
          ap2 _∙_ (emloop-β g₁) (emloop-β g₂)
          ==
          emloop-β (G.comp g₁ g₂) ∙
          F.pres-comp g₁ g₂
      emloop-comp-path = M.emloop-comp-path

  open EM₁Rec public using () renaming (f to EM₁-rec)

  module EM₁Level₁Rec {j} {C : Type j}
    {{C-level : has-level ⟨ 1 ⟩ C}}
    (embase* : C)
    (hom* : G →ᴳ (Ω^S-group 0 ⊙[ C , embase* ])) where

    module M = EM₁Rec' {{raise-level 1 C-level}}
                       embase* (GroupHom.f hom*) (GroupHom.pres-comp hom*)
                       (λ g₁ g₂ g₃ → =ₛ-in (prop-has-all-paths _ _))

    abstract
      f : EM₁ G → C
      f = M.f

      embase-β : f embase ↦ embase*
      embase-β = M.embase-β
      {-# REWRITE embase-β #-}

      emloop-β : (g : G.El) → ap f (emloop g) == GroupHom.f hom* g
      emloop-β = M.emloop-β

  open EM₁Level₁Rec public using () renaming (f to EM₁-level₁-rec)

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
