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

module _ (G : Group i) where

  postulate  -- HIT
    EM₁ : Type i
    embase' : EM₁
    emloop' : Group.El G → embase' == embase'
    emloop-comp' : ∀ g₁ g₂ → emloop' (Group.comp G g₁ g₂) == emloop' g₁ ∙ emloop' g₂
    emloop-coh' : ∀ g₁ g₂ g₃ →
      emloop-comp' (Group.comp G g₁ g₂) g₃ ∙ ap (λ l → l ∙ emloop' g₃) (emloop-comp' g₁ g₂) ∙ ∙-assoc (emloop' g₁) (emloop' g₂) (emloop' g₃)
      == ap emloop' (Group.assoc G g₁ g₂ g₃) ∙ emloop-comp' g₁ (Group.comp G g₂ g₃) ∙ ap (λ l → emloop' g₁ ∙ l) (emloop-comp' g₂ g₃)

  ⊙EM₁ : Ptd i
  ⊙EM₁ = ⊙[ EM₁ , embase' ]

module _ {G : Group i} where
  private
    module G = Group G

  embase = embase' G
  emloop = emloop' G
  emloop-comp = emloop-comp' G
  emloop-coh = emloop-coh' G

  -- instance
  --   EM₁-level : {n : ℕ₋₂} → has-level (S (S (S n))) (EM₁ G)
  --   EM₁-level {⟨-2⟩} = EM₁-level' G
  --   EM₁-level {S n} = raise-level _ EM₁-level


  abstract
    -- This was in the original paper, but is actually derivable.
    emloop-ident : emloop G.ident == idp
    emloop-ident = ! $ anti-whisker-right (emloop G.ident) $
      ap emloop (! $ G.unit-r G.ident) ∙ emloop-comp G.ident G.ident

  module EM₁Elim {j} {P : EM₁ G → Type j}
    -- {{_ : (x : EM₁ G) → has-level ⟨ 1 ⟩ (P x)}}
    (embase* : P embase)
    (emloop* : (g : G.El) → embase* == embase* [ P ↓ emloop g ])
    (emloop-comp* : (g₁ g₂ : G.El) →
       emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ᵈ emloop* g₂
       [ (λ p → embase* == embase* [ P ↓ p ]) ↓ emloop-comp g₁ g₂ ])
    (emloop-coh* : (g₁ g₂ g₃ : G.El) →
      emloop-comp* (G.comp g₁ g₂) g₃ ∙ᵈ (emloop-comp* g₁ g₂ ∙ᵈᵣ emloop* g₃) ∙ᵈ ∙ᵈ-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃)
      == ↓-ap-in (λ p → embase* == embase* [ P ↓ p ]) emloop (apd emloop* (G.assoc g₁ g₂ g₃)) ∙ᵈ emloop-comp* g₁ (G.comp g₂ g₃) ∙ᵈ (emloop* g₁ ∙ᵈₗ emloop-comp* g₂ g₃)
      [ (λ e → emloop* (G.comp (G.comp g₁ g₂) g₃) == emloop* g₁ ∙ᵈ (emloop* g₂ ∙ᵈ emloop* g₃) [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e ]) ↓ emloop-coh g₁ g₂ g₃ ])
    where

    postulate  -- HIT
      f : Π (EM₁ G) P
      embase-β : f embase ↦ embase*
    {-# REWRITE embase-β #-}

    postulate  -- HIT
      emloop-β : (g : G.El) → apd f (emloop g) == emloop* g

  open EM₁Elim public using () renaming (f to EM₁-elim)

  module EM₁Rec {j} {C : Type j}
    (embase* : C)
    (emloop* : (g : G.El) → embase* == embase*)
    (emloop-comp* : (g₁ g₂ : G.El) → emloop* (G.comp g₁ g₂) == emloop* g₁ ∙ emloop* g₂)
    (emloop-coh* : (g₁ g₂ g₃ : G.El) →
      emloop-comp* (G.comp g₁ g₂) g₃ ∙ ap (λ l → l ∙ emloop* g₃) (emloop-comp* g₁ g₂) ∙ ∙-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃) ==
      ap emloop* (G.assoc g₁ g₂ g₃) ∙ emloop-comp* g₁ (G.comp g₂ g₃) ∙ ap (λ l → emloop* g₁ ∙ l) (emloop-comp* g₂ g₃)) where

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
        φ = e₀₁ ∙ e₁₂ ∙ e₂₃

        ψ : s₀ == s₃
        ψ = e₀₄ ∙ e₄₅ ∙ e₅₃

        φ=ψ : φ == ψ
        φ=ψ = emloop-coh g₁ g₂ g₃

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
        φ* = e₀₁* ∙ e₁₂* ∙ e₂₃*

        ψ* : s₀* == s₃*
        ψ* = e₀₄* ∙ e₄₅* ∙ e₅₃*

        φ*=ψ* : φ* == ψ*
        φ*=ψ* = emloop-coh* g₁ g₂ g₃

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

        tt : ↓-cst-in s₃* == s₃**
        tt =
            ↓-cst-in-∙ (emloop g₁) (emloop g₂ ∙ emloop g₃) (emloop* g₁) (emloop* g₂ ∙ emloop* g₃)
          ∙ (emloop** g₁ ∙ᵈₗ ↓-cst-in-∙ (emloop g₂) (emloop g₃) (emloop* g₂) (emloop* g₃))


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
            =⟨ ↓-cst-in2-∙ᵣ {p' = emloop g₃} {q' = emloop* g₃} {p₀₁ = emloop-comp g₁ g₂} (emloop-comp* g₁ g₂) |in-ctx (λ y → e₀₁*' ∙ᵈ y ∙ᵈ f₃ ◃ e₂₃**) ⟩
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
        ee = {!!}

        emloop-coh** : φ** == ψ** [ (λ e → s₀** == s₃** [ (λ p → embase* == embase* [ P ↓ p ]) ↓ e ]) ↓ φ=ψ ]
        emloop-coh** = (! cc) ◃ ap (λ y → dd φ y) φ*=ψ* ◃ apd (λ y → dd y ψ*) φ=ψ ▹ ee

      module M = EM₁Elim {P = λ _ → C} embase* emloop** emloop-comp** emloop-coh**

    f = M.f

    emloop-β : (g : G.El) → ap f (emloop g) == emloop* g
    emloop-β g = {!!} -- M.emloop-β g

  open EM₁Rec public using () renaming (f to EM₁-rec)

  {-
  module EM₁Rec {j} {C : Type j}
    {{_ : has-level ⟨ 1 ⟩ C}} (embase* : C)
    (hom* : G →ᴳ (Ω^S-group 0 ⊙[ C , embase* ])) where

    private
      module M = EM₁Elim {P = λ _ → C}
        embase* (λ g → ↓-cst-in (GroupHom.f hom* g))
        (λ g₁ g₂ → ↓-cst-in2 (GroupHom.pres-comp hom* g₁ g₂)
                 ∙'ᵈ ↓-cst-in-∙ (emloop g₁) (emloop g₂)
                      (GroupHom.f hom* g₁) (GroupHom.f hom* g₂))

    f = M.f

    emloop-β : (g : G.El) → ap f (emloop g) == GroupHom.f hom* g
    emloop-β g = apd=cst-in {f = f} (M.emloop-β g)

  open EM₁Rec public using () renaming (f to EM₁-rec)
  -}

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
    -- TODO
    -- instance
    --   EM₁-conn : is-connected 0 (EM₁ G)
    --   EM₁-conn = has-level-in ([ embase ] , Trunc-elim
    --     (EM₁-elim
    --       {P = λ x → [ embase ] == [ x ]}
    --       -- {{λ _ → raise-level _ (=-preserves-level Trunc-level)}}
    --       idp
    --       (λ _ → prop-has-all-paths-↓)
    --       (λ _ _ → set-↓-has-all-paths-↓)))
