{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.EilenbergMacLane1.Core
open import lib.groups.Homomorphism
open import lib.groups.LoopSpace
open import lib.two-semi-categories.FundamentalCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.GroupToCategory

module lib.types.EilenbergMacLane1.Recursion {i} {G : Group i} where

private
  module G = Group G

module EM₁Rec' {j} {C : Type j}
  {{C-level : has-level 2 C}}
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

    Q : embase' G == embase → Type j
    Q p = embase* == embase* [ P ↓ p ]

    emloop** : ∀ g → Q (emloop g)
    emloop** g = ↓-cst-in (emloop* g)

    emloop-comp** : ∀ g₁ g₂ →
      emloop** (G.comp g₁ g₂) == emloop** g₁ ∙ᵈ emloop** g₂
        [ Q ↓ emloop-comp g₁ g₂ ]
    emloop-comp** g₁ g₂ =
      ↓-cst-in2 (emloop-comp* g₁ g₂) ▹
      ↓-cst-in-∙ (emloop g₁) (emloop g₂) (emloop* g₁) (emloop* g₂)

    module _ (g₁ g₂ g₃ : G.El) where

      s₀ : embase' G == embase
      s₀ = emloop (G.comp (G.comp g₁ g₂) g₃)

      s₁ : embase' G == embase
      s₁ = emloop (G.comp g₁ g₂) ∙ emloop g₃

      s₂ : embase' G == embase
      s₂ = (emloop g₁ ∙ emloop g₂) ∙ emloop g₃

      s₃ : embase' G == embase
      s₃ = emloop g₁ ∙ (emloop g₂ ∙ emloop g₃)

      s₄ : embase' G == embase
      s₄ = emloop (G.comp g₁ (G.comp g₂ g₃))

      s₅ : embase' G == embase
      s₅ = emloop g₁ ∙ emloop (G.comp g₂ g₃)

      e₀₁ : s₀ == s₁
      e₀₁ = emloop-comp (G.comp g₁ g₂) g₃

      e₁₂ : s₁ == s₂
      e₁₂ = ap (_∙ emloop g₃) (emloop-comp g₁ g₂)

      e₂₃ : s₂ == s₃
      e₂₃ = ∙-assoc (emloop g₁) (emloop g₂) (emloop g₃)

      e₀₄ : s₀ == s₄
      e₀₄ = ap emloop (G.assoc g₁ g₂ g₃)

      e₄₅ : s₄ == s₅
      e₄₅ = emloop-comp g₁ (G.comp g₂ g₃)

      e₅₃ : s₅ == s₃
      e₅₃ = ap (emloop g₁ ∙_) (emloop-comp g₂ g₃)

      φ : s₀ == s₃
      φ = ↯ (e₀₁ ◃∙ e₁₂ ◃∙ e₂₃ ◃∎)

      ψ : s₀ == s₃
      ψ = ↯ (e₀₄ ◃∙ e₄₅ ◃∙ e₅₃ ◃∎)

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
      e₁₂* = ap (_∙ emloop* g₃) (emloop-comp* g₁ g₂)

      e₂₃* : s₂* == s₃*
      e₂₃* = ∙-assoc (emloop* g₁) (emloop* g₂) (emloop* g₃)

      e₀₄* : s₀* == s₄*
      e₀₄* = ap emloop* (G.assoc g₁ g₂ g₃)

      e₄₅* : s₄* == s₅*
      e₄₅* = emloop-comp* g₁ (G.comp g₂ g₃)

      e₅₃* : s₅* == s₃*
      e₅₃* = ap (emloop* g₁ ∙_) (emloop-comp* g₂ g₃)

      φ* : s₀* == s₃*
      φ* = ↯ (e₀₁* ◃∙ e₁₂* ◃∙ e₂₃* ◃∎)

      ψ* : s₀* == s₃*
      ψ* = ↯ (e₀₄* ◃∙ e₄₅* ◃∙ e₅₃* ◃∎)

      φ*=ψ* : φ* == ψ*
      φ*=ψ* = =ₛ-out (emloop-coh* g₁ g₂ g₃)

      s₀** : Q s₀
      s₀** = emloop** (G.comp (G.comp g₁ g₂) g₃)

      s₁** : Q s₁
      s₁** = emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃

      s₂** : Q s₂
      s₂** = (emloop** g₁ ∙ᵈ emloop** g₂) ∙ᵈ emloop** g₃

      s₃** : Q s₃
      s₃** = emloop** g₁ ∙ᵈ (emloop** g₂ ∙ᵈ emloop** g₃)

      s₄** : Q s₄
      s₄** = emloop** (G.comp g₁ (G.comp g₂ g₃))

      s₅** : Q s₅
      s₅** = emloop** g₁ ∙ᵈ emloop** (G.comp g₂ g₃)

      e₀₁** : s₀** == s₁** [ Q ↓ e₀₁ ]
      e₀₁** = emloop-comp** (G.comp g₁ g₂) g₃

      e₁₂** : s₁** == s₂** [ Q ↓ e₁₂ ]
      e₁₂** = emloop-comp** g₁ g₂ ∙ᵈᵣ emloop** g₃

      e₂₃** : s₂** == s₃** [ Q ↓ e₂₃ ]
      e₂₃** = ∙ᵈ-assoc (emloop** g₁) (emloop** g₂) (emloop** g₃)

      e₀₄** : s₀** == s₄** [ Q ↓ e₀₄ ]
      e₀₄** = ↓-ap-in Q emloop (apd emloop** (G.assoc g₁ g₂ g₃))

      e₄₅** : s₄** == s₅** [ Q ↓ e₄₅ ]
      e₄₅** = emloop-comp** g₁ (G.comp g₂ g₃)

      e₅₃** : s₅** == s₃** [ Q ↓ e₅₃ ]
      e₅₃** = emloop** g₁ ∙ᵈₗ emloop-comp** g₂ g₃

      φ** : s₀** == s₃** [ Q ↓ φ ]
      φ** = e₀₁** ∙ᵈ e₁₂** ∙ᵈ e₂₃**

      ψ** : s₀** == s₃** [ Q ↓ ψ ]
      ψ** = e₀₄** ∙ᵈ e₄₅** ∙ᵈ e₅₃**

      s₃-path₁ : ↓-cst-in {p = s₃} s₃* ==
                 emloop** g₁ ∙ᵈ ↓-cst-in (emloop* g₂ ∙ emloop* g₃)
      s₃-path₁ = ↓-cst-in-∙ (emloop g₁) (emloop g₂ ∙ emloop g₃)
                            (emloop* g₁) (emloop* g₂ ∙ emloop* g₃)

      s₃-path₂' : ↓-cst-in (emloop* g₂ ∙ emloop* g₃) ==
                  emloop** g₂ ∙ᵈ emloop** g₃
      s₃-path₂' = ↓-cst-in-∙ (emloop g₂) (emloop g₃)
                             (emloop* g₂) (emloop* g₃)

      s₃-path₂ : emloop** g₁ ∙ᵈ ↓-cst-in (emloop* g₂ ∙ emloop* g₃) == s₃**
      s₃-path₂ = emloop** g₁ ∙ᵈₗ s₃-path₂'

      s₃-path : ↓-cst-in s₃* == s₃**
      s₃-path = s₃-path₁ ∙ s₃-path₂

      *-to-**-path : (r : s₀ == s₃) → s₀* == s₃* → s₀** == s₃** [ Q ↓ r ]
      *-to-**-path r q = ↓-cst-in2 {q = r} q ▹ s₃-path

      φ-step : *-to-**-path φ φ* == φ**
      φ-step =
        ↓-cst-in2 {q = φ} φ* ▹ s₃-path
          =⟨ (↓-cst-in2-∙ {p₀₁ = e₀₁} {p₁₂ = e₁₂ ∙ e₂₃}
                          e₀₁* (e₁₂* ∙ e₂₃*)) ∙'ᵈᵣ s₃-path ⟩
        (e₀₁*' ∙ᵈ ↓-cst-in2 {q = e₁₂ ∙ e₂₃} (e₁₂* ∙ e₂₃*)) ▹ s₃-path
          =⟨ ap (λ y → (e₀₁*' ∙ᵈ y) ▹ s₃-path) $
             ↓-cst-in2-∙ {p₀₁ = e₁₂} {p₁₂ = e₂₃} e₁₂* e₂₃* ⟩
        (e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ e₂₃*') ▹ s₃-path
          =⟨ ∙ᵈ-∙'ᵈ-assoc' e₀₁*' (e₁₂*' ∙ᵈ e₂₃*') s₃-path ⟩
        e₀₁*' ∙ᵈ (e₁₂*' ∙ᵈ e₂₃*') ▹ s₃-path
          =⟨ ap (e₀₁*' ∙ᵈ_) (∙ᵈ-∙'ᵈ-assoc' e₁₂*' e₂₃*' s₃-path) ⟩
        e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ e₂₃*' ▹ s₃-path
          =⟨ ap (λ y → e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ y) $
             ↓-cst-in-assoc {p₀ = emloop g₁} {p₁ = emloop g₂} {p₂ = emloop g₃}
                            (emloop* g₁) (emloop* g₂) (emloop* g₃) ⟩
        e₀₁*' ∙ᵈ e₁₂*' ∙ᵈ f₂ ◃ f₃ ◃ e₂₃**
          =⟨ ! (ap (e₀₁*' ∙ᵈ_) (◃▹-assoc e₁₂*' f₂ (f₃ ◃ e₂₃**))) ⟩
        e₀₁*' ∙ᵈ (e₁₂*' ▹ f₂) ∙ᵈ f₃ ◃ e₂₃**
          =⟨ ap (λ y → e₀₁*' ∙ᵈ y ∙ᵈ f₃ ◃ e₂₃**) $
             ↓-cst-in2-whisker-right {p' = emloop g₃} {q' = emloop* g₃}
                                     {p₀₁ = emloop-comp g₁ g₂}
                                     (emloop-comp* g₁ g₂) ⟩
        e₀₁*' ∙ᵈ (f₀ ◃ f₁) ∙ᵈ f₃ ◃ e₂₃**
          =⟨ ap (e₀₁*' ∙ᵈ_) (∙ᵈ-assoc f₀ f₁ (f₃ ◃ e₂₃**)) ⟩
        e₀₁*' ∙ᵈ f₀ ◃ f₁ ∙ᵈ f₃ ◃ e₂₃**
          =⟨ ! (◃▹-assoc e₀₁*' f₀ (f₁ ∙ᵈ f₃ ◃ e₂₃**)) ⟩
        e₀₁** ∙ᵈ f₁ ∙ᵈ f₃ ◃ e₂₃**
          =⟨ ! (ap (e₀₁** ∙ᵈ_) (◃▹-assoc f₁ f₃ e₂₃**)) ⟩
        e₀₁** ∙ᵈ (f₁ ▹ f₃) ∙ᵈ e₂₃**
          =⟨ ! (ap (λ y → e₀₁** ∙ᵈ y ∙ᵈ e₂₃**) (∙ᵈᵣ-∙'ᵈ f₁' f₃' (emloop** g₃))) ⟩
        φ** =∎
        where
        e₀₁*' : ↓-cst-in s₀* == ↓-cst-in s₁* [ Q ↓ e₀₁ ]
        e₀₁*' = ↓-cst-in2 {q = e₀₁} e₀₁*
        e₁₂*' : ↓-cst-in s₁* == ↓-cst-in s₂* [ Q ↓ e₁₂ ]
        e₁₂*' = ↓-cst-in2 {q = e₁₂} e₁₂*
        e₂₃*' : ↓-cst-in s₂* == ↓-cst-in s₃* [ Q ↓ e₂₃ ]
        e₂₃*' = ↓-cst-in2 {q = e₂₃} e₂₃*
        f₀ : ↓-cst-in (emloop* (G.comp g₁ g₂) ∙ emloop* g₃) ==
             emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃
        f₀ = ↓-cst-in-∙ (emloop (G.comp g₁ g₂)) (emloop g₃)
                        (emloop* (G.comp g₁ g₂)) (emloop* g₃)
        f₁' : emloop** (G.comp g₁ g₂) ==
              ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂)
                [ Q ↓ emloop-comp' G g₁ g₂ ]
        f₁' = ↓-cst-in2 {q = emloop-comp g₁ g₂} (emloop-comp* g₁ g₂)
        f₁ : emloop** (G.comp g₁ g₂) ∙ᵈ emloop** g₃ ==
             ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃
               [ Q ↓ ap (_∙ emloop' G g₃) (emloop-comp' G g₁ g₂) ]
        f₁ = f₁' ∙ᵈᵣ emloop** g₃
        f₂ : ↓-cst-in ((emloop* g₁ ∙ emloop* g₂) ∙ emloop* g₃) ==
             ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃
        f₂ = ↓-cst-in-∙ (emloop g₁ ∙ emloop g₂) (emloop g₃)
                        (emloop* g₁ ∙ emloop* g₂) (emloop* g₃)
        f₃' : ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ==
              emloop** g₁ ∙ᵈ emloop** g₂
        f₃' = ↓-cst-in-∙ (emloop g₁) (emloop g₂) (emloop* g₁) (emloop* g₂)
        f₃ : ↓-cst-in {p = emloop g₁ ∙ emloop g₂} (emloop* g₁ ∙ emloop* g₂) ∙ᵈ emloop** g₃ ==
             (emloop** g₁ ∙ᵈ emloop** g₂) ∙ᵈ emloop** g₃
        f₃ = f₃' ∙ᵈᵣ emloop** g₃

      ψ-step : *-to-**-path ψ ψ* == ψ**
      ψ-step =
        ↓-cst-in2 {q = ψ} ψ* ▹ s₃-path
          =⟨ ap (_▹ s₃-path) $
             ↓-cst-in2-∙ {p₀₁ = e₀₄} {p₁₂ = e₄₅ ∙ e₅₃}
                         e₀₄* (e₄₅* ∙ e₅₃*) ⟩
        (e₀₄*' ∙ᵈ ↓-cst-in2 {q = e₄₅ ∙ e₅₃} (e₄₅* ∙ e₅₃*)) ▹ s₃-path
          =⟨ ap (λ y → (e₀₄*' ∙ᵈ y) ▹ s₃-path) $
             ↓-cst-in2-∙ {p₀₁ = e₄₅} {p₁₂ = e₅₃} e₄₅* e₅₃* ⟩
        (e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*') ▹ s₃-path
          =⟨ ∙ᵈ-∙'ᵈ-assoc' e₀₄*' (e₄₅*' ∙ᵈ e₅₃*') s₃-path ⟩
        e₀₄*' ∙ᵈ (e₄₅*' ∙ᵈ e₅₃*') ▹ s₃-path
          =⟨ ap (e₀₄*' ∙ᵈ_) (∙ᵈ-∙'ᵈ-assoc' e₄₅*' e₅₃*' s₃-path) ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ s₃-path
          =⟨ ap (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ y) (∙=∙' s₃-path₁ s₃-path₂) ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ e₅₃*' ▹ (s₃-path₁ ∙' s₃-path₂)
          =⟨ ! $ ap (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y) $
             ∙'ᵈ-assoc e₅₃*' s₃-path₁ s₃-path₂ ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ (e₅₃*' ▹ s₃-path₁) ▹ s₃-path₂
          =⟨ ap (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y ▹ s₃-path₂) $
             ↓-cst-in2-whisker-left {p = emloop g₁} {q = emloop* g₁}
                                    {p₀₁' = emloop-comp g₂ g₃}
                                    (emloop-comp* g₂ g₃) ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ (f₀ ◃ f₁) ▹ s₃-path₂
          =⟨ ap (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ y) $
             ∙ᵈ-∙'ᵈ-assoc f₀ f₁ s₃-path₂ ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ (f₁ ▹ s₃-path₂)
          =⟨ ! $ ap (λ y → e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ y) $
             ∙ᵈₗ-∙'ᵈ f₁' s₃-path₂' (emloop** g₁) ⟩
        e₀₄*' ∙ᵈ e₄₅*' ∙ᵈ f₀ ◃ e₅₃**
          =⟨ ! (ap (e₀₄*' ∙ᵈ_) (◃▹-assoc e₄₅*' f₀ e₅₃**)) ⟩
        e₀₄*' ∙ᵈ e₄₅** ∙ᵈ e₅₃**
          =⟨ ap (_∙ᵈ e₄₅** ∙ᵈ e₅₃**) $
             ↓-cst-in2-ap emloop emloop* (G.assoc g₁ g₂ g₃) ⟩
        ψ** =∎
        where
        e₀₄*' : ↓-cst-in s₀* == ↓-cst-in s₄* [ Q ↓ e₀₄ ]
        e₀₄*' = ↓-cst-in2 {q = e₀₄} e₀₄*
        e₄₅*' : ↓-cst-in s₄* == ↓-cst-in s₅* [ Q ↓ e₄₅ ]
        e₄₅*' = ↓-cst-in2 {q = e₄₅} e₄₅*
        e₅₃*' : ↓-cst-in s₅* == ↓-cst-in s₃* [ Q ↓ e₅₃ ]
        e₅₃*' = ↓-cst-in2 {q = e₅₃} e₅₃*
        f₀ : ↓-cst-in (emloop* g₁ ∙ emloop* (G.comp g₂ g₃)) ==
             emloop** g₁ ∙ᵈ ↓-cst-in (emloop* (G.comp g₂ g₃))
        f₀ = ↓-cst-in-∙ (emloop g₁) (emloop' G (G.comp g₂ g₃))
                        (emloop* g₁) (emloop* (G.comp g₂ g₃))
        f₁' : emloop** (G.comp g₂ g₃) == ↓-cst-in (emloop* g₂ ∙ emloop* g₃)
                [ Q ↓ emloop-comp g₂ g₃ ]
        f₁' = ↓-cst-in2 {q = emloop-comp g₂ g₃} (emloop-comp* g₂ g₃)
        f₁ : emloop** g₁ ∙ᵈ emloop** (G.comp g₂ g₃) ==
             emloop** g₁ ∙ᵈ ↓-cst-in (emloop* g₂ ∙ emloop* g₃)
               [ Q ↓ ap (emloop g₁ ∙_) (emloop-comp g₂ g₃) ]
        f₁ = emloop** g₁ ∙ᵈₗ f₁'

      abstract
        emloop-coh** : φ** == ψ** [ (λ q → s₀** == s₃** [ Q ↓ q ]) ↓ φ=ψ ]
        emloop-coh** =
          ! φ-step ◃
          ap (λ p* → *-to-**-path φ p*) φ*=ψ* ◃
          apd (λ p → *-to-**-path p ψ*) φ=ψ ▹
          ψ-step

    module M = EM₁Elim {P = λ _ → C} {{λ _ → C-level}}
                       embase* emloop** emloop-comp** emloop-coh**

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
      → ap (ap f) (emloop-comp g₁ g₂) ◃∙
        ap-∙ f (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (emloop-β g₁) (emloop-β g₂) ◃∎
        =ₛ
        emloop-β (G.comp g₁ g₂) ◃∙
        emloop-comp* g₁ g₂ ◃∎
    emloop-comp-path g₁ g₂ = =ₛ-in $
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
  {{C-level : has-level 2 C}}
  (F : TwoSemiFunctor (group-to-cat G) (2-type-fundamental-cat C {{C-level}})) where

  private
    module F = TwoSemiFunctor F
    module M =
      EM₁Rec' {C = C} {{C-level}}
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
      → ap (ap f) (emloop-comp g₁ g₂) ◃∙
        ap-∙ f (emloop g₁) (emloop g₂) ◃∙
        ap2 _∙_ (emloop-β g₁) (emloop-β g₂) ◃∎
        =ₛ
        emloop-β (G.comp g₁ g₂) ◃∙
        F.pres-comp g₁ g₂ ◃∎
    emloop-comp-path = M.emloop-comp-path

open EM₁Rec public using () renaming (f to EM₁-rec)

module EM₁Level₁Rec {j} {C : Type j}
  {{C-level : has-level 1 C}}
  (embase* : C)
  (hom* : G →ᴳ (Ω^S-group 0 ⊙[ C , embase* ])) where

  module M =
    EM₁Rec' {{raise-level 1 C-level}}
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
