{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.KernelCstImage {i j k}
  {G : Group i} {H : Group j} (K : Group k)
  (φ : G →ᴳ H) (H-ab : is-abelian H) where

  open import groups.KernelImage {K = K} cst-hom φ H-ab
  open import groups.Cokernel φ H-ab

  Ker-cst-quot-Im : Ker/Im ≃ᴳ Coker
  Ker-cst-quot-Im = ≃-to-≃ᴳ (equiv to from to-from from-to) to-pres-comp where
    to : Ker/Im.El → Coker.El
    to = SetQuot-rec SetQuot-level to' quot-rel where
      to' : Ker.El (cst-hom {G = H} {H = K}) → Coker.El
      to' ker = q[ fst ker ]

    from : Coker.El → Ker/Im.El
    from = SetQuot-rec SetQuot-level from' quot-rel where
      from' : Group.El H → Ker/Im.El
      from' h = q[ h , idp ]

    abstract
      to-from : ∀ cok → to (from cok) == cok
      to-from = SetQuot-elim (λ _ → =-preserves-set SetQuot-level)
        (λ _ → idp)
        (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

      from-to : ∀ ker → from (to ker) == ker
      from-to = SetQuot-elim (λ _ → =-preserves-set SetQuot-level)
        (λ _ → ap q[_] $ ker-El=-out idp)
        (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _))

      to-pres-comp : preserves-comp Ker/Im.comp Coker.comp to
      to-pres-comp = SetQuot-elim
        (λ _ → Π-is-set λ _ → =-preserves-set SetQuot-level)
        (λ _ → SetQuot-elim
          (λ _ → =-preserves-set SetQuot-level)
          (λ _ → idp)
          (λ _ → prop-has-all-paths-↓ (SetQuot-level _ _)))
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuot-level _ _))
