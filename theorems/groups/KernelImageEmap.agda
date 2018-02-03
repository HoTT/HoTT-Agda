{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.KernelImage

module groups.KernelImageEmap where

module _ {i₀ i₁ j₀ j₁ k₀ k₁}
  {G₀ : Group i₀} {H₀ : Group j₀} {K₀ : Group k₀}
  {G₁ : Group i₁} {H₁ : Group j₁} {K₁ : Group k₁}
  {ψ₀ : H₀ →ᴳ K₀} {φ₀ : G₀ →ᴳ H₀} (H₀-ab : is-abelian H₀)
  {ψ₁ : H₁ →ᴳ K₁} {φ₁ : G₁ →ᴳ H₁} (H₁-ab : is-abelian H₁)
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
  (ψ₀∼ψ₁ : CommSquareᴳ ψ₀ ψ₁ ξH ξK) 
  (φ₀∼φ₁ : CommSquareᴳ φ₀ φ₁ ξG ξH) 
  where

  module ξG = GroupHom ξG
  module ξH = GroupHom ξH
  module ξK = GroupHom ξK
  module ψ₀ = GroupHom ψ₀
  module ψ₁ = GroupHom ψ₁
  module φ₀ = GroupHom φ₀
  module φ₁ = GroupHom φ₁

  private
    f : Ker/Im.El ψ₀ φ₀ H₀-ab → Ker/Im.El ψ₁ φ₁ H₁-ab
    f = SetQuot-rec to pres-rel
      where
        abstract
          ξh-in-Ker : ∀ h (ψ₀h=0 : ψ₀.f h == Group.ident K₀)
            → ψ₁.f (ξH.f h) == Group.ident K₁
          ξh-in-Ker h ψ₀h=0 = (! $ ψ₀∼ψ₁ □$ᴳ h) ∙ ap ξK.f ψ₀h=0 ∙ ξK.pres-ident 

        to : Ker.El ψ₀ → Ker/Im.El ψ₁ φ₁ H₁-ab
        to (h , ψ₀h=0) = q[ ξH.f h , ξh-in-Ker h ψ₀h=0 ]

        abstract
          pres-rel : ∀ {h h'} 
            → ker/im-rel ψ₀ φ₀ H₀-ab h h'
            → to h == to h'
          pres-rel {(h , _)} {(h' , _)} = Trunc-rec
            λ{(g , φg=h-h') → quot-rel
              [ ξG.f g , (! $ φ₀∼φ₁ □$ᴳ g) ∙ ap ξH.f φg=h-h' ∙ ξH.pres-diff h h' ]}

    abstract
      f-is-hom : preserves-comp (Ker/Im.comp ψ₀ φ₀ H₀-ab) (Ker/Im.comp ψ₁ φ₁ H₁-ab) f
      f-is-hom = SetQuot-elim
        (λ{(h , _) → SetQuot-elim
          (λ{(h' , _) → ap q[_] (Ker.El=-out ψ₁ (ξH.pres-comp h h'))})
          (λ _ → prop-has-all-paths-↓)})
        (λ _ → prop-has-all-paths-↓)

  Ker/Im-fmap : Ker/Im ψ₀ φ₀ H₀-ab →ᴳ Ker/Im ψ₁ φ₁ H₁-ab
  Ker/Im-fmap = group-hom f f-is-hom

module _ {i₀ i₁ j₀ j₁ k₀ k₁}
  {G₀ : Group i₀} {H₀ : Group j₀} {K₀ : Group k₀}
  {G₁ : Group i₁} {H₁ : Group j₁} {K₁ : Group k₁}
  {ψ₀ : H₀ →ᴳ K₀} {φ₀ : G₀ →ᴳ H₀} (H₀-ab : is-abelian H₀)
  {ψ₁ : H₁ →ᴳ K₁} {φ₁ : G₁ →ᴳ H₁} (H₁-ab : is-abelian H₁)
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
  (ψ₀∼ψ₁ : CommSquareᴳ ψ₀ ψ₁ ξH ξK)
  (φ₀∼φ₁ : CommSquareᴳ φ₀ φ₁ ξG ξH)
  (ξG-ise : is-equiv (GroupHom.f ξG))
  (ξH-ise : is-equiv (GroupHom.f ξH))
  (ξK-ise : is-equiv (GroupHom.f ξK))
  where

  private
    to : Ker/Im.El ψ₀ φ₀ H₀-ab → Ker/Im.El ψ₁ φ₁ H₁-ab
    to = GroupHom.f (Ker/Im-fmap H₀-ab H₁-ab ψ₀∼ψ₁ φ₀∼φ₁)
    
    from : Ker/Im.El ψ₁ φ₁ H₁-ab → Ker/Im.El ψ₀ φ₀ H₀-ab
    from = GroupHom.f (Ker/Im-fmap H₁-ab H₀-ab (CommSquareᴳ-inverse-v ψ₀∼ψ₁ ξH-ise ξK-ise) (CommSquareᴳ-inverse-v φ₀∼φ₁ ξG-ise ξH-ise))

    abstract
      to-from : ∀ x → to (from x) == x
      to-from = SetQuot-elim
        {{=-preserves-level ⟨⟩}}
        (λ{(h , _) → ap q[_] $ Ker.El=-out ψ₁ $ is-equiv.f-g ξH-ise h})
        (λ {h} {h'} _ → prop-has-all-paths-↓ {{has-level-apply SetQuot-is-set (to (from q[ h' ])) q[ h' ]}})

      from-to : ∀ x → from (to x) == x
      from-to = SetQuot-elim
        {{=-preserves-level ⟨⟩}}
        (λ{(h , _) → ap q[_] $ Ker.El=-out ψ₀ $ is-equiv.g-f ξH-ise h})
        (λ {h} {h'} _ → prop-has-all-paths-↓ {{has-level-apply SetQuot-is-set (from (to q[ h' ])) q[ h' ]}})

  Ker/Im-emap : Ker/Im ψ₀ φ₀ H₀-ab ≃ᴳ Ker/Im ψ₁ φ₁ H₁-ab
  Ker/Im-emap = Ker/Im-fmap H₀-ab H₁-ab ψ₀∼ψ₁ φ₀∼φ₁ ,
    is-eq to from to-from from-to
