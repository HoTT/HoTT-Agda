{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Pi
open import lib.NType2
open import lib.types.Paths
open import lib.types.EilenbergMacLane1.Core

module lib.types.EilenbergMacLane1.FunElim where

module _ {i} {G : Group i} where

  private
    module G = Group G

  module EM₁Level₁FunElim {j k} {B : EM₁ G → Type j} {C : EM₁ G → Type k}
    {{C-level : has-level 1 (C embase)}}
    (embase* : B embase → C embase)
    (emloop* : ∀ g b → transport C (emloop g) (embase* b) == embase* (transport B (emloop g) b))
    (emloop-comp* : ∀ g₁ g₂ b →
      emloop* (G.comp g₁ g₂) b ◃∙
      ap (λ p → embase* (transport B p b)) (emloop-comp g₁ g₂) ◃∙
      ap embase* (transp-∙ (emloop g₁) (emloop g₂) b) ◃∎
      =ₛ
      ap (λ p → transport C p (embase* b)) (emloop-comp g₁ g₂) ◃∙
      transp-∙ (emloop g₁) (emloop g₂) (embase* b) ◃∙
      ap (transport C (emloop g₂)) (emloop* g₁ b) ◃∙
      emloop* g₂ (transport B (emloop g₁) b) ◃∎)
    where

    emloop** : ∀ g → embase* == embase* [ (λ x → B x → C x) ↓ emloop g ]
    emloop** g = ↓-→-from-transp (λ= (emloop* g))

    private
      emloop-comp** : ∀ g₁ g₂ →
        emloop** (G.comp g₁ g₂) == emloop** g₁ ∙ᵈ emloop** g₂
          [ (λ p → embase* == embase* [ (λ x → B x → C x) ↓ p ]) ↓ emloop-comp g₁ g₂ ]
      emloop-comp** g₁ g₂ = step₁ ▹ step₂
        where
        intermediate' : ∀ b →
          transport C (emloop g₁ ∙ emloop g₂) (embase* b) ==
          embase* (transport B (emloop g₁ ∙ emloop g₂) b)
        intermediate' =
          comp-transp {B = B} {C = C}
                      {u = embase*} {u' = embase*} {u'' = embase*}
                      (emloop g₁) (emloop g₂)
                      (λ= (emloop* g₁)) (λ= (emloop* g₂))
        intermediate : embase* == embase* [ (λ x → B x → C x) ↓ emloop g₁ ∙ emloop g₂ ]
        intermediate = ↓-→-from-transp (λ= intermediate')
        step₁'' : ∀ b →
          app= (λ= (emloop* (G.comp g₁ g₂))) b ◃∙
          app= (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) b ◃∎
          =ₛ
          app= (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂)) b ◃∙
          app= (λ= intermediate') b ◃∎
        step₁'' b =
          app= (λ= (emloop* (G.comp g₁ g₂))) b ◃∙
          app= (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) b ◃∎
            =ₛ₁⟨ 0 & 1 & app=-β (emloop* (G.comp g₁ g₂)) b ⟩
          emloop* (G.comp g₁ g₂) b ◃∙
          app= (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) b ◃∎
            =ₛ₁⟨ 1 & 1 & ∘-ap (_$ b) (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂) ⟩
          emloop* (G.comp g₁ g₂) b ◃∙
          ap (λ p → embase* (transport B p b)) (emloop-comp g₁ g₂) ◃∎
            =ₛ⟨ post-rotate-in {p = _ ◃∙ _ ◃∎} (emloop-comp* g₁ g₂ b) ⟩
          ap (λ p → transport C p (embase* b)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (embase* b) ◃∙
          ap (transport C (emloop g₂)) (emloop* g₁ b) ◃∙
          emloop* g₂ (transport B (emloop g₁) b) ◃∙
          ! (ap embase* (transp-∙ (emloop g₁) (emloop g₂) b)) ◃∎
            =ₛ₁⟨ 2 & 1 & ap (ap (transport C (emloop g₂))) (! (app=-β (emloop* g₁) b)) ⟩
          ap (λ p → transport C p (embase* b)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (embase* b) ◃∙
          ap (transport C (emloop g₂)) (app= (λ= (emloop* g₁)) b) ◃∙
          emloop* g₂ (transport B (emloop g₁) b) ◃∙
          ! (ap embase* (transp-∙ (emloop g₁) (emloop g₂) b)) ◃∎
            =ₛ₁⟨ 3 & 1 & ! (app=-β (emloop* g₂) (transport B (emloop g₁) b)) ⟩
          ap (λ p → transport C p (embase* b)) (emloop-comp g₁ g₂) ◃∙
          transp-∙ (emloop g₁) (emloop g₂) (embase* b) ◃∙
          ap (transport C (emloop g₂)) (app= (λ= (emloop* g₁)) b) ◃∙
          app= (λ= (emloop* g₂)) (transport B (emloop g₁) b) ◃∙
          ! (ap embase* (transp-∙ (emloop g₁) (emloop g₂) b)) ◃∎
            =ₛ⟨ 1 & 4 & contract ⟩
          ap (λ p → transport C p (embase* b)) (emloop-comp g₁ g₂) ◃∙
          intermediate' b ◃∎
            =ₛ₁⟨ 0 & 1 & ap-∘ (_$ b) (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂) ⟩
          app= (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂)) b ◃∙
          intermediate' b ◃∎
            =ₛ₁⟨ 1 & 1 & ! (app=-β intermediate' b) ⟩
          app= (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂)) b ◃∙
          app= (λ= intermediate') b ◃∎ ∎ₛ
        step₁' :
          λ= (emloop* (G.comp g₁ g₂)) ∙
          ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)
          ==
          ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂) ∙
          λ= intermediate'
        step₁' =
          –>-is-inj (app=-equiv {A = B embase} {P = λ _ → C embase}
                                {f = transport C (emloop (G.comp g₁ g₂)) ∘ embase*}
                                {g = embase* ∘ transport B (emloop g₁ ∙ emloop g₂)})
                     _ _ $
          λ= $ λ b →
          app= (λ= (emloop* (G.comp g₁ g₂)) ∙
                ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) b
            =⟨ ap-∙ (_$ b) (λ= (emloop* (G.comp g₁ g₂)))
                           (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) ⟩
          app= (λ= (emloop* (G.comp g₁ g₂))) b ∙
          app= (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) b
            =⟨ =ₛ-out (step₁'' b) ⟩
          app= (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂)) b ∙
          app= (λ= intermediate') b
            =⟨ ∙-ap (_$ b) (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂))
                           (λ= intermediate') ⟩
          app= (ap (λ p → transport C p ∘ embase*) (emloop-comp g₁ g₂) ∙
                λ= intermediate') b =∎
        step₁ : emloop** (G.comp g₁ g₂) == intermediate
                  [ (λ p → embase* == embase* [ (λ x → B x → C x) ↓ p ]) ↓ emloop-comp g₁ g₂ ]
        step₁ =
          ap↓ ↓-→-from-transp $
          ↓-='-in $
          ∙'=∙ (λ= (emloop* (G.comp g₁ g₂)))
               (ap (λ p → embase* ∘ transport B p) (emloop-comp g₁ g₂)) ∙
          step₁'
        step₂ : intermediate == emloop** g₁ ∙ᵈ emloop** g₂
        step₂ = ↓-→-from-transp-∙ᵈ {B = B} {C = C} {p = emloop g₁} {q = emloop g₂}
                                   {u = embase*} {u' = embase*} {u'' = embase*}
                                   (λ= (emloop* g₁)) (λ= (emloop* g₂))

      module M =
        EM₁Level₁Elim
          {P = λ x → B x → C x}
          {{EM₁-prop-elim {P = λ x → has-level 1 (B x → C x)}
                          {{λ x → has-level-is-prop}}
                          (Π-level {B = λ _ → C embase} (λ _ → C-level))}}
          embase*
          emloop**
          emloop-comp**

      open M public
