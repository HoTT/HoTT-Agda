{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import groups.Cokernel
open import groups.Image
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
    φ-const-implies-ψ-is-inj : (∀ g →  φ.f g == H.ident) → is-injᴳ ψ
    φ-const-implies-ψ-is-inj φ-is-const =
      has-trivial-ker-is-injᴳ ψ λ h ψh=0 →
        Trunc-rec
          (λ{(g , φg=h) → ! φg=h ∙ φ-is-const g})
          (E.ker-sub-im h ψh=0)

    G-trivial-implies-ψ-is-inj : is-trivialᴳ G → is-injᴳ ψ
    G-trivial-implies-ψ-is-inj G-is-triv =
      φ-const-implies-ψ-is-inj λ g → ap φ.f (G-is-triv g) ∙ φ.pres-ident

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
              (λ hf → fst hf)
              (λ hf₁ hf₂ → φ-is-inj _ _ (snd hf₁ ∙ ! (snd hf₂)))

        from : Ker.El ψ → G.El
        from = λ k → From.ext k (uncurry E.ker-sub-im k)

        to-from : ∀ k → to (from k) == k
        to-from k = Ker.El=-out ψ $
          Trunc-elim
            {P = λ hf → φ.f (From.ext k hf) == fst k}
            (λ{(g , p) → p})
            (uncurry E.ker-sub-im k)

        from-to : ∀ g → from (to g) == g
        from-to g = From.ext-is-const (to g) (uncurry E.ker-sub-im (to g)) [ g , idp ]

  φ-inj-implies-G-iso-ker : is-injᴳ φ → G ≃ᴳ Ker.grp ψ
  φ-inj-implies-G-iso-ker φ-is-inj = G-to-ker , φ-inj-implies-G-to-ker-is-equiv φ-is-inj

  abstract
    K-trivial-implies-φ-is-surj : is-trivialᴳ K → is-surjᴳ φ
    K-trivial-implies-φ-is-surj K-is-triv h = E.ker-sub-im h (K-is-triv (ψ.f h))

  coker-to-K : (H-is-abelian : is-abelian H) → Coker φ H-is-abelian →ᴳ K
  coker-to-K H-is-abelian = record {M} where
    module M where
      module Cok = Coker φ H-is-abelian
      abstract
        f-rel : ∀ {h₁ h₂ : H.El} (h₁h₂⁻¹-in-im : SubgroupProp.prop (im-propᴳ φ) (H.diff h₁ h₂))
          → ψ.f h₁ == ψ.f h₂
        f-rel {h₁} {h₂} h₁h₂⁻¹-in-im = K.zero-diff-same _ _ $
          ! (ψ.pres-diff h₁ h₂) ∙ E.im-sub-ker (H.diff h₁ h₂) h₁h₂⁻¹-in-im

      f : Cok.El → K.El
      f = SetQuot-rec ψ.f f-rel
      abstract
        pres-comp : ∀ h₁ h₂ → f (Cok.comp h₁ h₂) == K.comp (f h₁) (f h₂)
        pres-comp = SetQuot-elim
          (λ h₁ → SetQuot-elim
            (λ h₂ → ψ.pres-comp h₁ h₂)
            (λ _ → prop-has-all-paths-↓))
          (λ _ → prop-has-all-paths-↓)

  abstract
    ψ-surj-implies-coker-to-K-is-equiv : (H-is-abelian : is-abelian H)
      → is-surjᴳ ψ → is-equiv (GroupHom.f (coker-to-K H-is-abelian))
    ψ-surj-implies-coker-to-K-is-equiv H-is-abelian ψ-is-surj =
      is-eq to from to-from from-to
      where
        module Cok = Coker φ H-is-abelian

        to : Cok.El → K.El
        to = GroupHom.f (coker-to-K H-is-abelian)

        module From (k : K.El)
          = ConstExt {A = hfiber ψ.f k} {B = Cok.El}
              (λ hf → q[ fst hf ])
              (λ{(h₁ , p₁) (h₂ , p₂) → quot-rel $
                E.ker-sub-im (H.diff h₁ h₂) $
                  ψ.pres-diff h₁ h₂ ∙ ap2 K.diff p₁ p₂ ∙ K.inv-r k})

        from : K.El → Cok.El
        from k = From.ext k (ψ-is-surj k)

        to-from : ∀ k → to (from k) == k
        to-from k = Trunc-elim
          {P = λ hf → to (From.ext k hf) == k}
          (λ{(h , p) → p})
          (ψ-is-surj k)

        from-to : ∀ c → from (to c) == c
        from-to = SetQuot-elim
          (λ h → From.ext-is-const (ψ.f h) (ψ-is-surj (ψ.f h)) [ h , idp ])
          (λ _ → prop-has-all-paths-↓)

  ψ-surj-implies-coker-iso-K : (H-is-abelian : is-abelian H)
    → is-surjᴳ ψ → Coker φ H-is-abelian ≃ᴳ K
  ψ-surj-implies-coker-iso-K H-is-abelian ψ-is-surj =
    coker-to-K H-is-abelian , ψ-surj-implies-coker-to-K-is-equiv H-is-abelian ψ-is-surj

  -- right split lemma
  module _ (H-is-abelian : is-abelian H) (φ-inj : is-injᴳ φ)
    (χ : K →ᴳ H) (χ-inv-r : (k : Group.El K) → GroupHom.f (ψ ∘ᴳ χ) k == k) where

    {- Splitting Lemma - Right Split
       Assume an exact sequence:

                 φ   ψ
           0 → G → H → K

       where H is abelian. If ψ has a right inverse χ, then H == G × K. Over
       this path φ becomes the natural injection and ψ the natural projection.
    -}

    private
      module χ = GroupHom χ

      {- H ≃ᴳ Ker ψ × Im χ -}

      ker-part : H →ᴳ Ker ψ
      ker-part = Ker.inject-lift ψ
        (hom-comp H (H , H-is-abelian) (idhom H) (inv-hom (H , H-is-abelian) ∘ᴳ (χ ∘ᴳ ψ)))
        (λ h →
          ψ.f (H.comp h (H.inv (χ.f (ψ.f h))))
            =⟨ ψ.pres-comp h (H.inv (χ.f (ψ.f h))) ⟩
          K.comp (ψ.f h) (ψ.f (H.inv (χ.f (ψ.f h))))
            =⟨ ! (χ.pres-inv (ψ.f h))
               |in-ctx (λ w → K.comp (ψ.f h) (ψ.f w)) ⟩
          K.comp (ψ.f h) (ψ.f (χ.f (K.inv (ψ.f h))))
            =⟨ χ-inv-r (K.inv (ψ.f h)) |in-ctx K.comp (ψ.f h) ⟩
          K.comp (ψ.f h) (K.inv (ψ.f h))
            =⟨ K.inv-r (ψ.f h) ⟩
          K.ident ∎)

      abstract
        ker-part-kerψ : (ker : Ker.El ψ) → GroupHom.f ker-part (fst ker) == ker
        ker-part-kerψ (h , p) = Ker.El=-out ψ $
          H.comp h (H.inv (χ.f (ψ.f h)))
            =⟨ p |in-ctx (λ w → H.comp h (H.inv (χ.f w))) ⟩
          H.comp h (H.inv (χ.f K.ident))
            =⟨ χ.pres-ident |in-ctx (λ w → H.comp h (H.inv w)) ⟩
          H.comp h (H.inv H.ident)
            =⟨ H.inv-ident |in-ctx H.comp h ⟩
          H.comp h H.ident
            =⟨ H.unit-r h ⟩
          h =∎

        ker-part-imχ : (im : Im.El χ) → GroupHom.f ker-part (fst im) == Ker.ident ψ
        ker-part-imχ (h , s) = Trunc-rec
          (λ {(k , p) → Ker.El=-out ψ $
            H.comp h (H.inv (χ.f (ψ.f h)))
              =⟨ ! p |in-ctx (λ w → H.comp w (H.inv (χ.f (ψ.f w)))) ⟩
            H.comp (χ.f k) (H.inv (χ.f (ψ.f (χ.f k))))
              =⟨ χ-inv-r k |in-ctx (λ w → H.comp (χ.f k) (H.inv (χ.f w))) ⟩
            H.comp (χ.f k) (H.inv (χ.f k))
              =⟨ H.inv-r (χ.f k) ⟩
            H.ident
              =∎})
          s

      im-part : H →ᴳ Im χ
      im-part = im-lift χ ∘ᴳ ψ

      abstract
        im-part-kerψ : (ker : Ker.El ψ) → GroupHom.f im-part (fst ker) == Im.ident χ
        im-part-kerψ (h , p) = Im.El=-out χ (ap χ.f p ∙ χ.pres-ident)

        im-part-imχ : (im : Im.El χ) → GroupHom.f im-part (fst im) == im
        im-part-imχ (h , s) = Trunc-rec {{has-level-apply (Im.El-level χ) _ _}}
            (λ {(k , p) → Im.El=-out χ $
              χ.f (ψ.f h)        =⟨ ! p |in-ctx (χ.f ∘ ψ.f) ⟩
              χ.f (ψ.f (χ.f k))  =⟨ χ-inv-r k |in-ctx χ.f ⟩
              χ.f k              =⟨ p ⟩
              h                  =∎})
            s

      decomp : H →ᴳ Ker ψ ×ᴳ Im χ
      decomp = ×ᴳ-fanout ker-part im-part

      decomp-is-equiv : is-equiv (GroupHom.f decomp)
      decomp-is-equiv = is-eq _ dinv decomp-dinv dinv-decomp
        where
        dinv : Group.El (Ker ψ ×ᴳ Im χ) → H.El
        dinv ((h₁ , _) , (h₂ , _)) = H.comp h₁ h₂

        abstract
          decomp-dinv : ∀ s → GroupHom.f decomp (dinv s) == s
          decomp-dinv ((h₁ , kr) , (h₂ , im)) = pair×=
            (GroupHom.f ker-part (H.comp h₁ h₂)
               =⟨ GroupHom.pres-comp ker-part h₁ h₂ ⟩
             Ker.comp ψ (GroupHom.f ker-part h₁) (GroupHom.f ker-part h₂)
               =⟨ ap2 (Ker.comp ψ) (ker-part-kerψ (h₁ , kr)) (ker-part-imχ (h₂ , im)) ⟩
             Ker.comp ψ (h₁ , kr) (Ker.ident ψ)
               =⟨ Ker.unit-r ψ (h₁ , kr) ⟩
             (h₁ , kr)
               =∎)
            (GroupHom.f im-part (H.comp h₁ h₂)
               =⟨ GroupHom.pres-comp im-part h₁ h₂ ⟩
             Im.comp χ (GroupHom.f im-part h₁) (GroupHom.f im-part h₂)
               =⟨ ap2 (Im.comp χ) (im-part-kerψ (h₁ , kr)) (im-part-imχ (h₂ , im)) ⟩
             Im.comp χ (Im.ident χ) (h₂ , im)
               =⟨ Im.unit-l χ (h₂ , im) ⟩
             (h₂ , im) ∎)

          dinv-decomp : ∀ h → dinv (GroupHom.f decomp h) == h
          dinv-decomp h =
            H.comp (H.comp h (H.inv (χ.f (ψ.f h)))) (χ.f (ψ.f h))
              =⟨ H.assoc h (H.inv (χ.f (ψ.f h))) (χ.f (ψ.f h)) ⟩
            H.comp h (H.comp (H.inv (χ.f (ψ.f h))) (χ.f (ψ.f h)))
              =⟨ H.inv-l (χ.f (ψ.f h)) |in-ctx H.comp h ⟩
            H.comp h H.ident
              =⟨ H.unit-r h ⟩
            h ∎

      decomp-equiv : H.El ≃ Group.El (Ker ψ ×ᴳ Im χ)
      decomp-equiv = (_ , decomp-is-equiv)

      decomp-iso : H ≃ᴳ Ker ψ ×ᴳ Im χ
      decomp-iso = decomp , decomp-is-equiv

      {- K == Im χ -}

      K-iso-Imχ : K ≃ᴳ Im χ
      K-iso-Imχ = surjᴳ-and-injᴳ-iso (im-lift χ) (im-lift-is-surj χ) inj where
        abstract
          inj = has-trivial-ker-is-injᴳ (im-lift χ)
                  (λ k p → ! (χ-inv-r k) ∙ ap ψ.f (ap fst p) ∙ ψ.pres-ident)

    φ-inj-and-ψ-has-rinv-split : H ≃ᴳ G ×ᴳ K
    φ-inj-and-ψ-has-rinv-split =
      ×ᴳ-emap (φ-inj-implies-G-iso-ker φ-inj ⁻¹ᴳ) (K-iso-Imχ ⁻¹ᴳ) ∘eᴳ decomp-iso

    abstract
      φ-inj-and-ψ-has-rinv-implies-φ-comm-inl : CommSquareᴳ φ ×ᴳ-inl
        (idhom _) (–>ᴳ φ-inj-and-ψ-has-rinv-split )
      φ-inj-and-ψ-has-rinv-implies-φ-comm-inl = comm-sqrᴳ λ g → pair×=
        (ap (GroupIso.g (φ-inj-implies-G-iso-ker φ-inj))
              (ker-part-kerψ (GroupHom.f G-to-ker g))
          ∙ GroupIso.g-f (φ-inj-implies-G-iso-ker φ-inj) g)
        (im-sub-ker-out φ ψ E.im-sub-ker g)

    φ-inj-and-ψ-has-rinv-implies-ψ-comm-snd : CommSquareᴳ ψ (×ᴳ-snd {G = G})
      (–>ᴳ φ-inj-and-ψ-has-rinv-split ) (idhom _)
    φ-inj-and-ψ-has-rinv-implies-ψ-comm-snd = comm-sqrᴳ λ h → idp

abstract
  pre∘-is-exact : ∀ {i j k l} {G : Group i} {H : Group j} {K : Group k} {L : Group l}
    (φ : G →ᴳ H) {ψ : H →ᴳ K} {ξ : K →ᴳ L} → is-surjᴳ φ → is-exact ψ ξ → is-exact (ψ ∘ᴳ φ) ξ
  pre∘-is-exact φ {ψ = ψ} φ-is-surj ψ-ξ-is-exact = record {
    ker-sub-im = λ k → im-sub-im-∘ ψ φ φ-is-surj k ∘ ker-sub-im ψ-ξ-is-exact k;
    im-sub-ker = λ k → im-sub-ker ψ-ξ-is-exact k ∘ im-∘-sub-im ψ φ k}

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

  G-trivial-implies-H-iso-ker :
    is-trivialᴳ G → H ≃ᴳ Ker.grp ξ
  G-trivial-implies-H-iso-ker G-is-triv
    = EL2.φ-inj-implies-G-iso-ker $
        EL1.G-trivial-implies-ψ-is-inj G-is-triv

  L-trivial-implies-coker-iso-K : (H-is-abelian : is-abelian H)
    → is-trivialᴳ L → Coker φ H-is-abelian ≃ᴳ K
  L-trivial-implies-coker-iso-K H-is-abelian L-is-triv
    = EL1.ψ-surj-implies-coker-iso-K H-is-abelian $
        EL2.K-trivial-implies-φ-is-surj L-is-triv

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
      im-sub-ker = λ h₁ → Trunc-rec
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
        Trunc-rec
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

abstract
  equiv-preserves'-exact : ∀ {i₀ i₁ j₀ j₁ l₀ l₁}
    {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁} {K₀ : Group l₀} {K₁ : Group l₁}
    {φ₀ : G₀ →ᴳ H₀} {ψ₀ : H₀ →ᴳ K₀} {φ₁ : G₁ →ᴳ H₁} {ψ₁ : H₁ →ᴳ K₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
    → CommSquareᴳ φ₀ φ₁ ξG ξH → CommSquareᴳ ψ₀ ψ₁ ξH ξK
    → is-equiv (GroupHom.f ξG) → is-equiv (GroupHom.f ξH) → is-equiv (GroupHom.f ξK)
    → is-exact φ₁ ψ₁ → is-exact φ₀ ψ₀
  equiv-preserves'-exact cs₀ cs₁ ξG-ise ξH-ise ξK-ise ex =
    equiv-preserves-exact
      (CommSquareᴳ-inverse-v cs₀ ξG-ise ξH-ise)
      (CommSquareᴳ-inverse-v cs₁ ξH-ise ξK-ise)
      (is-equiv-inverse ξG-ise)
      (is-equiv-inverse ξH-ise)
      (is-equiv-inverse ξK-ise)
      ex
