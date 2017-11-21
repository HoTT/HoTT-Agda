{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.KernelCstImageCst {i j k}
  (G : Group i) (H : Group j) (K : Group k)
  (H-ab : is-abelian H) where

  private
    module H = Group H

  open import groups.KernelImage {G = G} {H = H} {K = K} cst-hom cst-hom H-ab

  Ker-cst-quot-Im-cst : Ker/Im ≃ᴳ H
  Ker-cst-quot-Im-cst = ≃-to-≃ᴳ (equiv to from to-from from-to) to-pres-comp where
    to : Ker/Im.El → H.El
    to = SetQuot-rec to' to-rel where
      to' : Ker.El (cst-hom {G = H} {H = K}) → H.El
      to' ker = fst ker

      abstract
        to-rel : ∀ {h₁ h₂} → ker/im-rel' h₁ h₂ → h₁ == h₂
        to-rel {h₁} {h₂} = Trunc-rec
          λ{(_ , 0=h₁h₂⁻¹) → H.zero-diff-same h₁ h₂ (! 0=h₁h₂⁻¹)}

    from : H.El → Ker/Im.El
    from h = q[ h , idp ]

    abstract
      to-from : ∀ h → to (from h) == h
      to-from h = idp

      from-to : ∀ k/i → from (to k/i) == k/i
      from-to = SetQuot-elim
        (λ _ → ap q[_] $ ker-El=-out idp)
        (λ _ → prop-has-all-paths-↓)

      to-pres-comp : preserves-comp Ker/Im.comp H.comp to
      to-pres-comp = SetQuot-elim
        (λ _ → SetQuot-elim
          (λ _ → idp)
          (λ _ → prop-has-all-paths-↓))
        (λ _ → prop-has-all-paths-↓)
