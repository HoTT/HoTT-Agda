{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.cubical.Square
open import lib.types.Group
open import lib.types.EilenbergMacLane1.Core

module lib.types.EilenbergMacLane1.PathElim where

module _ {i} (G : Group i) where

  private
    module G = Group G

  module EM₁Level₂PathElim {k} {C : Type k}
    {{C-level : has-level 2 C}}
    (f₁ f₂ : EM₁ G → C)
    (embase* : f₁ embase == f₂ embase)
    (emloop* : ∀ g →
      Square embase* (ap f₁ (emloop g))
             (ap f₂ (emloop g)) embase*)
    (emloop-comp* : ∀ g₁ g₂ →
      emloop* (G.comp g₁ g₂) ⊡v∙
      ap (ap f₂) (emloop-comp' G g₁ g₂)
      ==
      ap (ap f₁) (emloop-comp' G g₁ g₂) ∙v⊡
      ↓-='-square-comp (emloop* g₁) (emloop* g₂))
    where

    private
      module M =
        EM₁Level₁Elim {i} {G}
          {P = λ x → f₁ x == f₂ x}
          {{λ x → has-level-apply C-level _ _}}
          embase*
          (λ g → ↓-='-from-square (emloop* g))
          (λ g₁ g₂ →
            ↓-='-from-square-comp-path (emloop-comp g₁ g₂)
                                       (emloop* g₁)
                                       (emloop* g₂)
                                       (emloop* (G.comp g₁ g₂))
                                       (emloop-comp* g₁ g₂))

    open M public

  module EM₁Level₂PathConstElim {k} {C : Type k}
    {{C-level : has-level 2 C}}
    (f : EM₁ G → C) (c : C)
    (embase* : f embase == c)
    (emloop* : ∀ g →
      Square embase* (ap f (emloop g))
             idp embase*)
    (emloop-comp* : ∀ g₁ g₂ →
      emloop* (G.comp g₁ g₂)
      ==
      (ap (ap f) (emloop-comp' G g₁ g₂) ∙
       ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡
      (emloop* g₁ ⊡h emloop* g₂))
    where

    private

      emloop** : ∀ g → Square embase* (ap f (emloop g))
                                      (ap (cst c) (emloop' G g)) embase*
      emloop** g = emloop* g ⊡v∙ ! (ap-cst c (emloop g))

      emloop-comp** : ∀ g₁ g₂ →
        emloop** (G.comp g₁ g₂) ⊡v∙ ap (ap (cst c)) (emloop-comp' G g₁ g₂)
        ==
        ap (ap f) (emloop-comp g₁ g₂) ∙v⊡
        ↓-='-square-comp (emloop** g₁) (emloop** g₂)
      emloop-comp** g₁ g₂ =
        (emloop* (G.comp g₁ g₂) ⊡v∙ ! (ap-cst c (emloop (G.comp g₁ g₂)))) ⊡v∙ ap (ap (cst c)) (emloop-comp g₁ g₂)
          =⟨ ⊡v∙-assoc (emloop* (G.comp g₁ g₂))
                       (! (ap-cst c (emloop (G.comp g₁ g₂))))
                       (ap (ap (cst c)) (emloop-comp g₁ g₂)) ⟩
        emloop* (G.comp g₁ g₂) ⊡v∙
        (! (ap-cst c (emloop (G.comp g₁ g₂))) ∙
        ap (ap (cst c)) (emloop-comp g₁ g₂))
          =⟨ ap (emloop* (G.comp g₁ g₂) ⊡v∙_) $ =ₛ-out $
             ! (ap-cst c (emloop (G.comp g₁ g₂))) ◃∙
             ap (ap (cst c)) (emloop-comp g₁ g₂) ◃∎
               =ₛ⟨ pre-rotate'-in $
                   post-rotate-in {p = _ ◃∎} $
                   homotopy-naturality-to-cst (ap (cst c)) idp (ap-cst c) (emloop-comp g₁ g₂) ⟩
             ! (ap-cst c (emloop g₁ ∙ emloop g₂)) ◃∎
               =ₛ⟨ !-=ₛ (ap-cst-coh c (emloop g₁) (emloop g₂)) ⟩
             ! (ap2 _∙_ (ap-cst c (emloop g₁)) (ap-cst c (emloop g₂))) ◃∙
             ! (ap-∙ (cst c) (emloop g₁) (emloop g₂)) ◃∎
               =ₛ₁⟨ 0 & 1 & !-ap2 _∙_ (ap-cst c (emloop g₁)) (ap-cst c (emloop g₂)) ⟩
             ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))) ◃∙
             ! (ap-∙ (cst c) (emloop g₁) (emloop g₂)) ◃∎
               =ₛ₁⟨ 1 & 1 & !ap-∙=∙-ap (cst c) (emloop g₁) (emloop g₂) ⟩
             ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))) ◃∙
             ∙-ap (cst c) (emloop g₁) (emloop g₂) ◃∎ ∎ₛ
           ⟩
        emloop* (G.comp g₁ g₂) ⊡v∙
        (ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))) ∙
        ∙-ap (cst c) (emloop g₁) (emloop g₂))
          =⟨ ! $ ⊡v∙-assoc (emloop* (G.comp g₁ g₂))
                           (ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))))
                           (∙-ap (cst c) (emloop g₁) (emloop g₂)) ⟩
        (emloop* (G.comp g₁ g₂) ⊡v∙
        ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂)))) ⊡v∙
        ∙-ap (cst c) (emloop g₁) (emloop g₂)
          =⟨ ap (λ s → (s ⊡v∙
                       ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂)))) ⊡v∙
                       ∙-ap (cst c) (emloop g₁) (emloop g₂))
                (emloop-comp* g₁ g₂) ⟩
        (((ap (ap f) (emloop-comp' G g₁ g₂) ∙
        ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡
        emloop* g₁ ⊡h emloop* g₂) ⊡v∙
        ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂)))) ⊡v∙
        ∙-ap (cst c) (emloop g₁) (emloop g₂)
          =⟨ ap (_⊡v∙ ∙-ap (cst c) (emloop g₁) (emloop g₂)) $
             ((ap (ap f) (emloop-comp' G g₁ g₂) ∙
             ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡
             emloop* g₁ ⊡h emloop* g₂) ⊡v∙
             ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂)))
               =⟨ ∙v⊡-⊡v∙-comm
                    (ap (ap f) (emloop-comp' G g₁ g₂) ∙ ap-∙ f (emloop g₁) (emloop g₂))
                    (emloop* g₁ ⊡h emloop* g₂)
                    (ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂)))) ⟩
             (ap (ap f) (emloop-comp' G g₁ g₂) ∙
             ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡
             ((emloop* g₁ ⊡h emloop* g₂) ⊡v∙
             ap2 _∙_ (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))))
               =⟨ ap ((ap (ap f) (emloop-comp' G g₁ g₂) ∙
                       ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡_) $
                  ⊡h-⊡v∙-comm (emloop* g₁) (emloop* g₂)
                              (! (ap-cst c (emloop g₁))) (! (ap-cst c (emloop g₂))) ⟩
             (ap (ap f) (emloop-comp' G g₁ g₂) ∙
             ap-∙ f (emloop g₁) (emloop g₂)) ∙v⊡
             (emloop** g₁ ⊡h emloop** g₂)
               =⟨ ∙v⊡-assoc (ap (ap f) (emloop-comp' G g₁ g₂))
                            (ap-∙ f (emloop g₁) (emloop g₂))
                            (emloop** g₁ ⊡h emloop** g₂) ⟩
             ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡
             (ap-∙ f (emloop g₁) (emloop g₂) ∙v⊡
             (emloop** g₁ ⊡h emloop** g₂)) =∎
           ⟩
        (ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡
        (ap-∙ f (emloop g₁) (emloop g₂) ∙v⊡
        (emloop** g₁ ⊡h emloop** g₂))) ⊡v∙
        ∙-ap (cst c) (emloop g₁) (emloop g₂)
          =⟨ ∙v⊡-⊡v∙-comm (ap (ap f) (emloop-comp' G g₁ g₂))
                          (ap-∙ f (emloop g₁) (emloop g₂) ∙v⊡ (emloop** g₁ ⊡h emloop** g₂))
                          (∙-ap (cst c) (emloop g₁) (emloop g₂)) ⟩
        ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡
        (ap-∙ f (emloop g₁) (emloop g₂) ∙v⊡ emloop** g₁ ⊡h emloop** g₂) ⊡v∙ ∙-ap (cst c) (emloop g₁) (emloop g₂)
          =⟨ ap (ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡_) $
             ∙v⊡-⊡v∙-comm (ap-∙ f (emloop g₁) (emloop g₂))
                          (emloop** g₁ ⊡h emloop** g₂)
                          (∙-ap (cst c) (emloop g₁) (emloop g₂)) ⟩
        ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡
        ↓-='-square-comp' (emloop** g₁) (emloop** g₂)
          =⟨ ap (ap (ap f) (emloop-comp' G g₁ g₂) ∙v⊡_) $
             ↓-='-square-comp'=↓-='-square-comp {f = f} {g = cst c}
                                                (emloop** g₁) (emloop** g₂) ⟩
        ap (ap f) (emloop-comp g₁ g₂) ∙v⊡
        ↓-='-square-comp (emloop** g₁) (emloop** g₂) =∎

      module M =
        EM₁Level₂PathElim {k} {C}
          {{C-level}}
          f (cst c)
          embase*
          emloop**
          emloop-comp**

    open M public
