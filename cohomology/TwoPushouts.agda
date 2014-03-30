{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.TwoPushouts where

--        g     h
--     B --> C --> D    K = A ⊔^B C / (f,g)        d₁ = A <- B -> C
--    f|     |     |    L = K ⊔^C D / (left,h)     d₂ = K <- C -> D
--     v     v     v                               d  = A <- B -> D
--     A --> K --> L
--

module _ {i} {A B C : Type i} 
  (f : B → A) (g : B → C) where

  private
    d₁ : Span
    d₁ = span A C B f g

  module _ {D : Type i} (h : C → D) where

    private
      d₂ : Span
      d₂ = span (Pushout d₁) D C right h

      d : Span
      d = span A D B f (h ∘ g)

      into : Pushout d -> Pushout d₂
      into = PushoutRec.f 
        (left ∘ left)
        right
        (λ b → ap left (glue b) ∙ glue (g b))

      out : Pushout d₂ → Pushout d
      out = PushoutRec.f
        (PushoutRec.f left (right ∘ h) glue)
        right
        (λ _ → idp)

      abstract
        into-out : (l : Pushout d₂) → into (out l) == l
        into-out = Pushout-elim 
          (Pushout-elim 
            (λ a → idp) 
            (λ c → ! (glue c)) 
            (λ b → ↓-='-in 
              (ap left (glue b)
                 =⟨ ! (∙-unit-r _) ⟩
               ap left (glue b) ∙ idp
                 =⟨ ! (!-inv-r (glue (g b))) 
                   |in-ctx (λ w → ap left (glue b) ∙ w) ⟩
               ap left (glue b) ∙ (glue (g b) ∙ ! (glue (g b)))
                 =⟨ ! (∙-assoc (ap left (glue b)) (glue (g b)) _) ⟩
               (ap left (glue b) ∙ glue (g b)) ∙ ! (glue (g b))
                 =⟨ ∙=∙' (ap left (glue b) ∙ glue (g b)) (! (glue (g b))) ⟩
               (ap left (glue b) ∙ glue (g b)) ∙' ! (glue (g b))
                 =⟨ ! (PushoutRec.glue-β 
                         (left ∘ left) right
                         (λ b → ap left (glue b) ∙ glue (g b)) b)
                   |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
               ap into (glue b) ∙' ! (glue (g b))
                 =⟨ ! (PushoutRec.glue-β left (right ∘ h) glue b)
                    |in-ctx (λ w → ap into w ∙' ! (glue (g b))) ⟩
               ap into (ap (out ∘ left) (glue b)) ∙' ! (glue (g b))
                 =⟨ ∘-ap into (out ∘ left) (glue b) 
                   |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
               ap (into ∘ out ∘ left) (glue b) ∙' ! (glue (g b)) ∎)))
          (λ d → idp)
          (λ c → ↓-app=idf-in 
            (! (glue c) ∙' glue c
               =⟨ ∙'=∙ (! (glue c)) (glue c) ⟩
             ! (glue c) ∙ glue c
               =⟨ !-inv-l (glue c) ⟩
             idp
               =⟨ (! (PushoutRec.glue-β {d = d₂} 
                        (PushoutRec.f left (right ∘ h) glue) 
                        right (λ _ → idp) c))
                 |in-ctx (λ w → ap into w) ⟩
             ap into (ap out (glue c))
               =⟨ ∘-ap into out (glue c) ⟩
             ap (into ∘ out) (glue c)
               =⟨ ! (∙-unit-r _) ⟩
             ap (into ∘ out) (glue c) ∙ idp ∎ ))

        out-into : (l : Pushout d) → out (into l) == l
        out-into = Pushout-elim 
          (λ a → idp) 
          (λ d → idp) 
          (λ b → ↓-app=idf-in 
            (idp ∙' glue b
               =⟨ ∙'-unit-l _ ⟩
             glue b
               =⟨ ! (∙-unit-r _) ⟩
             glue b ∙ idp
               =⟨ ! (PushoutRec.glue-β {d = d₂}
                        (PushoutRec.f left (right ∘ h) glue) 
                        right (λ _ → idp) (g b))
                 |in-ctx (λ w → glue b ∙ w) ⟩
             glue b ∙ ap out (glue (g b))
               =⟨ ! (PushoutRec.glue-β left (right ∘ h) glue b)
                 |in-ctx (λ w → w ∙ ap out (glue (g b))) ⟩
             ap (out ∘ left) (glue b) ∙ ap out (glue (g b))
               =⟨ ap-∘ out left (glue b) 
                 |in-ctx (λ w → w ∙ ap out (glue (g b))) ⟩
             ap out (ap left (glue b)) ∙ ap out (glue (g b))
               =⟨ ∙-ap out (ap left (glue b)) (glue (g b)) ⟩
             ap out (ap left (glue b) ∙ glue (g b))
               =⟨ ! (PushoutRec.glue-β {d = d}
                        (left ∘ left) right 
                    (λ b → ap left (glue b) ∙ glue (g b)) b)
                 |in-ctx (λ w → ap out w) ⟩
             ap out (ap into (glue b))
               =⟨ ∘-ap out into (glue b) ⟩
             ap (out ∘ into) (glue b)
               =⟨ ! (∙-unit-r _) ⟩
             ap (out ∘ into) (glue b) ∙ idp ∎))


    two-pushouts-equiv : Pushout d ≃ Pushout d₂
    two-pushouts-equiv = equiv into out into-out out-into
