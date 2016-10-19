{-# OPTIONS --without-K #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt

-- A collection of useful lemmas about exactness

module groups.Exactness where

module Exact {i j k} {G : Group i} {H : Group j} {K : Group k}
  {φ : G →ᴳ H} {ψ : H →ᴳ K} (φ-ψ-is-exact : is-exact φ ψ) where

  private
    module G = Group G
    module H = Group H
    module K = Group K
    module φ = GroupHom φ
    module ψ = GroupHom ψ
    module E = is-exact φ-ψ-is-exact

  abstract
    G-trivial-implies-ψ-is-inj : is-trivialᴳ G → is-injᴳ ψ
    G-trivial-implies-ψ-is-inj G-is-triv =
      has-trivial-ker-is-injᴳ ψ λ h ψh=0 →
        Trunc-rec (H.El-is-set _ _)
          (λ{(g , φg=h) → ! φg=h ∙ ap φ.f (G-is-triv g) ∙ φ.pres-ident})
          (E.ker-sub-im h ψh=0)

  G-to-ker : G →ᴳ Ker.grp ψ
  G-to-ker = Ker.inject-lift ψ φ (λ g → E.im-sub-ker (φ.f g) [ g , idp ])

  abstract
    φ-inj-implies-G-to-ker-is-equiv : is-injᴳ φ → is-equiv (GroupHom.f G-to-ker)
    φ-inj-implies-G-to-ker-is-equiv φ-is-inj = is-eq _ from to-from from-to
      where
        to : G.El → Ker.El ψ
        to = GroupHom.f G-to-ker

        module From (k : Ker.El ψ)
          = ConstExt {A = hfiber φ.f (fst k)} {B = G.El}
              G.El-is-set (λ hf → fst hf)
              (λ hf₁ hf₂ → φ-is-inj _ _ (snd hf₁ ∙ ! (snd hf₂)))

        from : Ker.El ψ → G.El
        from = λ k → From.cst-extend k (uncurry E.ker-sub-im k)

        to-from : ∀ k → to (from k) == k
        to-from k = Subtype=-out (Ker.P.subEl-prop ψ) $
          Trunc-elim
            {P = λ hf → φ.f (From.cst-extend k hf) == fst k}
            (λ _ → H.El-is-set _ _)
            (λ{(g , p) → p})
            (uncurry E.ker-sub-im k)

        from-to : ∀ g → from (to g) == g
        from-to g = From.cst-extend-is-const (to g) (uncurry E.ker-sub-im (to g)) [ g , idp ]

    K-trivial-implies-φ-is-surj : is-trivialᴳ K → is-surjᴳ φ
    K-trivial-implies-φ-is-surj K-is-triv h = E.ker-sub-im h (K-is-triv (ψ.f h))

  coker-to-K : (H-is-abelian : is-abelian H) → Coker.grp H-is-abelian φ →ᴳ K
  coker-to-K H-is-abelian = record {
    f = SetQuot-rec K.El-is-set
      (λ h → ψ.f h)
      (λ {h₁} {h₂} h₁h₂⁻¹-in-im →
        K.zero-diff-same _ _ $ ! (ψ.pres-diff h₁ h₂) ∙ E.im-sub-ker (H.diff h₁ h₂) h₁h₂⁻¹-in-im);
    pres-comp = SetQuot-elim
      (λ _ → Π-is-set λ _ → =-preserves-set K.El-is-set)
      (λ h₁ → SetQuot-elim
        (λ _ → =-preserves-set K.El-is-set)
        (λ h₂ → ψ.pres-comp h₁ h₂)
        (λ _ → prop-has-all-paths-↓ (K.El-is-set _ _)))
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → K.El-is-set _ _))}

  abstract
    ψ-surj-implies-coker-to-K-is-equiv : (H-is-abelian : is-abelian H)
      → is-surjᴳ ψ → is-equiv (GroupHom.f (coker-to-K H-is-abelian))
    ψ-surj-implies-coker-to-K-is-equiv H-is-abelian ψ-is-surj =
      is-eq to from to-from from-to
      where
        module Cok = Coker H-is-abelian φ

        to : Cok.El → K.El
        to = GroupHom.f (coker-to-K H-is-abelian)

        module From (k : K.El)
          = ConstExt {A = hfiber ψ.f k} {B = Cok.El}
              Cok.El-is-set (λ hf → q[ fst hf ])
              (λ{(h₁ , p₁) (h₂ , p₂) →
                quot-relᴳ {P = Cok.npropᴳ} {g₁ = h₁} {g₂ = h₂} $
                  E.ker-sub-im (H.diff h₁ h₂) $
                    ψ.pres-diff h₁ h₂ ∙ ap2 K.diff p₁ p₂ ∙ K.inv-r k})

        from : K.El → Cok.El
        from k = From.cst-extend k (ψ-is-surj k)

        to-from : ∀ k → to (from k) == k
        to-from k = Trunc-elim
          {P = λ hf → to (From.cst-extend k hf) == k}
          (λ _ → K.El-is-set _ _)
          (λ{(h , p) → p})
          (ψ-is-surj k)

        from-to : ∀ c → from (to c) == c
        from-to = SetQuot-elim
          (λ _ → =-preserves-set Cok.El-is-set)
          (λ h → From.cst-extend-is-const (ψ.f h) (ψ-is-surj (ψ.f h)) [ h , idp ])
          (λ _ → prop-has-all-paths-↓ (Cok.El-is-set _ _))

module Exact2 {i j k l} {G : Group i} {H : Group j} {K : Group k} {L : Group l}
  {φ : G →ᴳ H} {ψ : H →ᴳ K} {ξ : K →ᴳ L}
  (φ-ψ-is-exact : is-exact φ ψ) (ψ-ξ-is-exact : is-exact ψ ξ) where

  private
    module G = Group G
    module H = Group H
    module K = Group K
    module L = Group L
    module φ = GroupHom φ
    module ψ = GroupHom ψ
    module ξ = GroupHom ξ
    module E1 = is-exact φ-ψ-is-exact
    module E2 = is-exact ψ-ξ-is-exact
    {- [L] for "lemmas" -}
    module EL1 = Exact φ-ψ-is-exact
    module EL2 = Exact ψ-ξ-is-exact

  abstract
    G-trivial-and-L-trivial-implies-H-iso-K :
      is-trivialᴳ G → is-trivialᴳ L → H ≃ᴳ K
    G-trivial-and-L-trivial-implies-H-iso-K G-is-triv L-is-triv
      = surjᴳ-and-injᴳ-iso ψ
          (EL2.K-trivial-implies-φ-is-surj L-is-triv)
          (EL1.G-trivial-implies-ψ-is-inj G-is-triv)

abstract
  equiv-preserves-exact : ∀ {i₀ i₁ j₀ j₁ l₀ l₁}
    {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁} {K₀ : Group l₀} {K₁ : Group l₁}
    {φ₀ : G₀ →ᴳ H₀} {ψ₀ : H₀ →ᴳ K₀} {φ₁ : G₁ →ᴳ H₁} {ψ₁ : H₁ →ᴳ K₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
    → CommSquareᴳ φ₀ φ₁ ξG ξH → CommSquareᴳ ψ₀ ψ₁ ξH ξK
    → is-equiv (GroupHom.f ξG) → is-equiv (GroupHom.f ξH) → is-equiv (GroupHom.f ξK)
    → is-exact φ₀ ψ₀ → is-exact φ₁ ψ₁
  equiv-preserves-exact {K₀ = K₀} {K₁} {φ₀ = φ₀} {ψ₀} {φ₁} {ψ₁} {ξG} {ξH} {ξK}
    (comm-sqrᴳ φ□) (comm-sqrᴳ ψ□) ξG-is-equiv ξH-is-equiv ξK-is-equiv exact₀
    = record {
      im-sub-ker = λ h₁ → Trunc-rec (SubgroupProp.level (ker-propᴳ ψ₁) h₁)
        (λ{(g₁ , φ₁g₁=h₁) →
          ψ₁.f h₁
            =⟨ ap ψ₁.f $ ! $ ξH.f-g h₁ ⟩
          ψ₁.f (ξH.f (ξH.g h₁))
            =⟨ ! $ ψ□ (ξH.g h₁) ⟩
          ξK.f (ψ₀.f (ξH.g h₁))
            =⟨ ap ξK.f $ im-sub-ker exact₀ (ξH.g h₁) [ ξG.g g₁ ,_ $
                φ₀.f (ξG.g g₁)
                  =⟨ ! (ξH.g-f (φ₀.f (ξG.g g₁))) ⟩
                ξH.g (ξH.f (φ₀.f (ξG.g g₁)))
                  =⟨ ap ξH.g $ φ□ (ξG.g g₁) ∙ ap φ₁.f (ξG.f-g g₁) ∙ φ₁g₁=h₁ ⟩
                ξH.g h₁
                  =∎ ] ⟩
          ξK.f (Group.ident K₀)
            =⟨ ξK.pres-ident ⟩
          Group.ident K₁
            =∎});
      ker-sub-im = λ h₁ ψ₁h₁=0 →
        Trunc-rec (SubgroupProp.level (im-propᴳ φ₁) h₁)
          (λ{(g₀ , φ₀g₀=ξH⁻¹h₁) → [ ξG.f g₀ ,_ $
            φ₁.f (ξG.f g₀)
              =⟨ ! $ φ□ g₀ ⟩
            ξH.f (φ₀.f g₀)
              =⟨ ap ξH.f φ₀g₀=ξH⁻¹h₁ ⟩
            ξH.f (ξH.g h₁)
              =⟨ ξH.f-g h₁ ⟩
            h₁
              =∎ ]})
          (ker-sub-im exact₀ (ξH.g h₁) $
            ψ₀.f (ξH.g h₁)
              =⟨ ! $ ξK.g-f (ψ₀.f (ξH.g h₁)) ⟩
            ξK.g (ξK.f (ψ₀.f (ξH.g h₁)))
              =⟨ ap ξK.g $ ψ□ (ξH.g h₁) ∙ ap ψ₁.f (ξH.f-g h₁) ∙ ψ₁h₁=0 ⟩
            ξK.g (Group.ident K₁)
              =⟨ GroupHom.pres-ident ξK.g-hom ⟩
            Group.ident K₀
              =∎)}
    where
      module φ₀ = GroupHom φ₀
      module φ₁ = GroupHom φ₁
      module ψ₀ = GroupHom ψ₀
      module ψ₁ = GroupHom ψ₁
      module ξG = GroupIso (ξG , ξG-is-equiv)
      module ξH = GroupIso (ξH , ξH-is-equiv)
      module ξK = GroupIso (ξK , ξK-is-equiv)

