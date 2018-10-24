{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1
open import homotopy.EM1HSpace
open import homotopy.EM1HSpaceAssoc

module homotopy.EilenbergMacLaneFunctor where

open EMExplicit

module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module φ = GroupHom φ

    EM₁-fmap-hom : G →ᴳ Ω^S-group 0 (⊙EM₁ H)
    EM₁-fmap-hom = group-hom f f-preserves-comp
      where
        f : Group.El G → embase' H == embase
        f g = emloop (φ.f g)
        f-preserves-comp : ∀ g₁ g₂ → f (Group.comp G g₁ g₂) == f g₁ ∙ f g₂
        f-preserves-comp g₁ g₂ =
          emloop (φ.f (Group.comp G g₁ g₂))
            =⟨ ap emloop (φ.pres-comp g₁ g₂) ⟩
          emloop (Group.comp H (φ.f g₁) (φ.f g₂))
            =⟨ emloop-comp' H (φ.f g₁) (φ.f g₂) ⟩
          emloop (φ.f g₁) ∙ emloop (φ.f g₂) =∎

    module EM₁FmapRec =
      EM₁Level₁Rec {G = G} {C = EM₁ H}
                  {{EM₁-level₁ H {⟨-2⟩}}}
                  embase
                  EM₁-fmap-hom

  abstract
    EM₁-fmap : EM₁ G → EM₁ H
    EM₁-fmap = EM₁FmapRec.f

    EM₁-fmap-embase-β : EM₁-fmap embase ↦ embase
    EM₁-fmap-embase-β = EM₁FmapRec.embase-β
    {-# REWRITE EM₁-fmap-embase-β #-}

    EM₁-fmap-emloop-β : ∀ g → ap EM₁-fmap (emloop g) == emloop (φ.f g)
    EM₁-fmap-emloop-β = EM₁FmapRec.emloop-β

  ⊙EM₁-fmap : ⊙EM₁ G ⊙→ ⊙EM₁ H
  ⊙EM₁-fmap = EM₁-fmap , idp

module _ {i j k} {G : Group i} {H : Group j} {K : Group k} (ψ : H →ᴳ K) (φ : G →ᴳ H) where

  EM₁-fmap-∘ : EM₁-fmap (ψ ∘ᴳ φ) ∼ EM₁-fmap ψ ∘ EM₁-fmap φ
  EM₁-fmap-∘ =
    EM₁-set-elim
      {P = λ x → EM₁-fmap (ψ ∘ᴳ φ) x == EM₁-fmap ψ (EM₁-fmap φ x)}
      {{λ x → has-level-apply (EM₁-level₁ K) _ _}}
      idp $
    λ g → ↓-='-in' $
    ap (EM₁-fmap ψ ∘ EM₁-fmap φ) (emloop g)
      =⟨ ap-∘ (EM₁-fmap ψ) (EM₁-fmap φ) (emloop g) ⟩
    ap (EM₁-fmap ψ) (ap (EM₁-fmap φ) (emloop g))
      =⟨ ap (ap (EM₁-fmap ψ)) (EM₁-fmap-emloop-β φ g) ⟩
    ap (EM₁-fmap ψ) (emloop (GroupHom.f φ g))
      =⟨ EM₁-fmap-emloop-β ψ (GroupHom.f φ g) ⟩
    emloop (GroupHom.f (ψ ∘ᴳ φ) g)
      =⟨ ! (EM₁-fmap-emloop-β (ψ ∘ᴳ φ) g) ⟩
    ap (EM₁-fmap (ψ ∘ᴳ φ)) (emloop g) =∎

  ⊙EM₁-fmap-∘ : ⊙EM₁-fmap (ψ ∘ᴳ φ) ⊙∼ ⊙EM₁-fmap ψ ⊙∘ ⊙EM₁-fmap φ
  ⊙EM₁-fmap-∘ = EM₁-fmap-∘ , idp

module _ {i} (G : Group i) where

  EM₁-fmap-idhom : EM₁-fmap (idhom G) ∼ idf (EM₁ G)
  EM₁-fmap-idhom =
    EM₁-set-elim
      {P = λ x → EM₁-fmap (idhom G) x == idf (EM₁ G) x}
      {{λ x → has-level-apply (EM₁-level₁ G) (EM₁-fmap (idhom G) x) x}}
      idp $
    λ g → ↓-='-in' $ ! $
    ap (EM₁-fmap (idhom G)) (emloop g)
      =⟨ EM₁-fmap-emloop-β (idhom G) g ⟩
    emloop g
      =⟨ ! (ap-idf (emloop g)) ⟩
    ap (idf (EM₁ G)) (emloop g) =∎

  ⊙EM₁-fmap-idhom : ⊙EM₁-fmap (idhom G) ⊙∼ ⊙idf (⊙EM₁ G)
  ⊙EM₁-fmap-idhom = EM₁-fmap-idhom , idp

module _ {i j} (G : AbGroup i) (H : AbGroup j) (φ : AbGroup.grp G →ᴳ AbGroup.grp H) where

  ⊙EM-fmap : ∀ n → ⊙EM G n ⊙→ ⊙EM H n
  ⊙EM-fmap O = ⊙Ω-fmap (⊙EM₁-fmap φ)
  ⊙EM-fmap (S n) = ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap φ))

  EM-fmap : ∀ n → EM G n → EM H n
  EM-fmap n = fst (⊙EM-fmap n)

module _ {i j k} (G : AbGroup i) (H : AbGroup j) (K : AbGroup k) (ψ : H →ᴬᴳ K) (φ : G →ᴬᴳ H) where

  private
    module G = AbGroup G
    module H = AbGroup H
    module K = AbGroup K

  ⊙EM-fmap-∘ : ∀ n → ⊙EM-fmap G K (ψ ∘ᴳ φ) n == ⊙EM-fmap H K ψ n ⊙∘ ⊙EM-fmap G H φ n
  ⊙EM-fmap-∘ O =
    ⊙Ω-fmap (⊙EM₁-fmap (ψ ∘ᴳ φ))
      =⟨ ap ⊙Ω-fmap (⊙λ= (⊙EM₁-fmap-∘ ψ φ)) ⟩
    ⊙Ω-fmap (⊙EM₁-fmap ψ ⊙∘ ⊙EM₁-fmap φ)
      =⟨ ⊙Ω-fmap-∘ (⊙EM₁-fmap ψ) (⊙EM₁-fmap φ) ⟩
    ⊙Ω-fmap (⊙EM₁-fmap ψ) ⊙∘ ⊙Ω-fmap (⊙EM₁-fmap φ) =∎
  ⊙EM-fmap-∘ (S n) =
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap (ψ ∘ᴳ φ)))
      =⟨ ap (⊙Trunc-fmap ∘ ⊙Susp^-fmap n) (⊙λ= (⊙EM₁-fmap-∘ ψ φ)) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap ψ ⊙∘ ⊙EM₁-fmap φ))
      =⟨ ap ⊙Trunc-fmap (⊙Susp^-fmap-∘ n (⊙EM₁-fmap ψ) (⊙EM₁-fmap φ)) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap ψ) ⊙∘ ⊙Susp^-fmap n (⊙EM₁-fmap φ))
      =⟨ ! (⊙λ= (⊙Trunc-fmap-∘ (⊙Susp^-fmap n (⊙EM₁-fmap ψ)) (⊙Susp^-fmap n (⊙EM₁-fmap φ)))) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap ψ)) ⊙∘ ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap φ)) =∎

  EM-fmap-∘ : ∀ n → EM-fmap G K (ψ ∘ᴳ φ) n == EM-fmap H K ψ n ∘ EM-fmap G H φ n
  EM-fmap-∘ n = ap fst (⊙EM-fmap-∘ n)

module _ {i} (G : AbGroup i) where

  private
    module G = AbGroup G
  open EM₁HSpace G using (mult; mult-emloop-β)

  EM₁-neg : EM₁ G.grp → EM₁ G.grp
  EM₁-neg = EM₁-fmap (inv-hom G)

  abstract
    EM₁-neg-emloop-β : ∀ g → ap EM₁-neg (emloop g) == ! (emloop g)
    EM₁-neg-emloop-β g =
      ap EM₁-neg (emloop g)
        =⟨ EM₁-fmap-emloop-β (inv-hom G) g ⟩
      emloop (G.inv g)
        =⟨ emloop-inv g ⟩
      ! (emloop g) =∎

    EM₁-neg-! : ∀ (p : embase' G.grp == embase)
      → ap EM₁-neg p == ! p
    EM₁-neg-! p =
      transport (λ q → ap EM₁-neg q == ! q)
                (<–-inv-r (emloop-equiv G.grp) p) $
      EM₁-neg-emloop-β (<– (emloop-equiv G.grp) p)

    EM₁-neg-inv-l : ∀ (x : EM₁ G.grp)
      → mult (EM₁-neg x) x == embase
    EM₁-neg-inv-l =
      EM₁-set-elim
        {P = λ x → mult (EM₁-neg x) x == embase}
        {{λ x → has-level-apply (EM₁-level₁ G.grp) _ _}}
        idp $ λ g →
      ↓-='-in-=ₛ $ !ₛ $
      ap (λ x → mult (EM₁-neg x) x) (emloop g) ◃∙
      idp ◃∎
        =ₛ⟨ 1 & 1 & expand [] ⟩
      ap (λ x → mult (EM₁-neg x) x) (emloop g) ◃∎
        =ₛ₁⟨ ! (ap2-diag (λ x y → mult (EM₁-neg x) y) (emloop g)) ⟩
      ap2 (λ x y → mult (EM₁-neg x) y) (emloop g) (emloop g) ◃∎
        =ₛ⟨ ap2-out (λ x y → mult (EM₁-neg x) y) (emloop g) (emloop g) ⟩
      ap (λ x → mult (EM₁-neg x) embase) (emloop g) ◃∙
      ap (λ y → y) (emloop g) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-idf (emloop g) ⟩
      ap (λ x → mult (EM₁-neg x) embase) (emloop g) ◃∙
      emloop g ◃∎
        =ₛ₁⟨ 0 & 1 & ap-∘ (λ x → mult x embase) EM₁-neg (emloop g) ⟩
      ap (λ x → mult x embase) (ap EM₁-neg (emloop g)) ◃∙
      emloop g ◃∎
        =ₛ₁⟨ 0 & 1 & ap (ap (λ x → mult x embase)) (EM₁-neg-emloop-β g) ⟩
      ap (λ x → mult x embase) (! (emloop g)) ◃∙
      emloop g ◃∎
        =ₛ₁⟨ 0 & 1 & ap-! (λ x → mult x embase) (emloop g) ⟩
      ! (ap (λ x → mult x embase) (emloop g)) ◃∙
      emloop g ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (mult-emloop-β g embase) ⟩
      ! (emloop g) ◃∙
      emloop g ◃∎
        =ₛ₁⟨ !-inv-l (emloop g) ⟩
      idp ◃∎
        =ₛ₁⟨ 1 & 0 & ! (ap-cst embase (emloop g)) ⟩
      idp ◃∙
      ap (cst embase) (emloop g) ◃∎ ∎ₛ

    EM₁-neg-inv-r : ∀ (x : EM₁ G.grp)
      → mult x (EM₁-neg x) == embase
    EM₁-neg-inv-r =
      EM₁-set-elim
        {P = λ x → mult x (EM₁-neg x) == embase}
        {{λ x → has-level-apply (EM₁-level₁ G.grp) _ _}}
        idp $ λ g →
      ↓-='-in-=ₛ $ !ₛ $
      ap (λ x → mult x (EM₁-neg x)) (emloop g) ◃∙
      idp ◃∎
        =ₛ⟨ 1 & 1 & expand [] ⟩
      ap (λ x → mult x (EM₁-neg x)) (emloop g) ◃∎
        =ₛ₁⟨ ! (ap2-diag (λ x y → mult x (EM₁-neg y)) (emloop g)) ⟩
      ap2 (λ x y → mult x (EM₁-neg y)) (emloop g) (emloop g) ◃∎
        =ₛ⟨ ap2-out (λ x y → mult x (EM₁-neg y)) (emloop g) (emloop g) ⟩
      ap (λ x → mult x embase) (emloop g) ◃∙
      ap EM₁-neg (emloop g) ◃∎
        =ₛ₁⟨ 0 & 1 & mult-emloop-β g embase ⟩
      emloop g ◃∙
      ap EM₁-neg (emloop g) ◃∎
        =ₛ₁⟨ 1 & 1 & EM₁-neg-emloop-β g ⟩
      emloop g ◃∙
      ! (emloop g) ◃∎
        =ₛ₁⟨ !-inv-r (emloop g) ⟩
      idp ◃∎
        =ₛ₁⟨ 1 & 0 & ! (ap-cst embase (emloop g)) ⟩
      idp ◃∙
      ap (λ _ → embase) (emloop g) ◃∎ ∎ₛ

  EM-neg : ∀ (n : ℕ) → EM G n → EM G n
  EM-neg n = EM-fmap G G (inv-hom G) n

  private
    -- superseded by Susp-flip-EM-neg
    Susp-flip-EM₁-neg : EM-neg 2 ∼ Trunc-fmap Susp-flip
    Susp-flip-EM₁-neg =
      Trunc-elim {{λ t → =-preserves-level (EM-level G 2)}} $
      Susp-elim
        {P = λ s → EM-neg 2 [ s ]₂ == Trunc-fmap Susp-flip [ s ]₂}
        (ap [_]₂ (merid embase))
        (! (ap [_]₂ (merid embase))) $
      λ x → ↓-='-in-=ₛ $
      ap [_]₂ (merid embase) ◃∙
      ap (Trunc-fmap Susp-flip ∘ [_]₂) (merid x) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-∘ [_]₂ Susp-flip (merid x) ⟩
      ap [_]₂ (merid embase) ◃∙
      ap [_]₂ (ap Susp-flip (merid x)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap (ap [_]₂) (SuspFlip.merid-β x) ⟩
      ap [_]₂ (merid embase) ◃∙
      ap [_]₂ (! (merid x)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap (ap [_]₂) (! (!-! (merid embase))) ⟩
      ap [_]₂ (! (! (merid embase))) ◃∙
      ap [_]₂ (! (merid x)) ◃∎
        =ₛ⟨ ap-seq-=ₛ [_]₂ (∙-!-seq (merid x ◃∙ ! (merid embase) ◃∎)) ⟩
      ap [_]₂ (! (η x)) ◃∎
        =ₛ₁⟨ ap-! [_]₂ (η x) ⟩
      ! (ap [_]₂ (η x)) ◃∎
        =ₛ₁⟨ cancels-inverse (ap [_]₂ (η x)) (ap [_]₂ (η (EM₁-neg x))) $
             ap [_]₂ (η x) ∙ ap [_]₂ (η (EM₁-neg x))
               =⟨ ∙-ap [_]₂ (η x) (η (EM₁-neg x)) ⟩
             ap [_]₂ (η x ∙ η (EM₁-neg x))
               =⟨ ap (<– (=ₜ-equiv [ north ]₂ [ north ]₂)) $
                  [ η x ∙ η (EM₁-neg x) ]₁
                    =⟨ ! (comp (EM₁-neg x) x) ⟩
                  [ η (mult (EM₁-neg x) x) ]₁
                    =⟨ ap ([_]₁ ∘ η) (EM₁-neg-inv-l x) ⟩
                  [ η embase ]₁
                    =⟨ ap [_]₁ (!-inv-r (merid embase)) ⟩
                  [ idp ]₁ =∎ ⟩
             idp =∎ ⟩
      ap [_]₂ (η (EM₁-neg x)) ◃∎
        =ₛ⟨ ap-seq-∙ [_]₂ (merid (EM₁-neg x) ◃∙ ! (merid embase) ◃∎) ⟩
      ap [_]₂ (merid (EM₁-neg x)) ◃∙
      ap [_]₂ (! (merid embase)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap (ap [_]₂) (! (SuspFmap.merid-β EM₁-neg x)) ⟩
      ap [_]₂ (ap (Susp-fmap EM₁-neg) (merid x)) ◃∙
      ap [_]₂ (! (merid embase)) ◃∎
        =ₛ₁⟨ 0 & 1 & ∘-ap [_]₂ (Susp-fmap EM₁-neg) (merid x) ⟩
      ap (EM-neg 2 ∘ [_]₂) (merid x) ◃∙
      ap [_]₂ (! (merid embase)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! [_]₂ (merid embase) ⟩
      ap (EM-neg 2 ∘ [_]₂) (merid x) ◃∙
      ! (ap [_]₂ (merid embase)) ◃∎ ∎ₛ
      where
      open EM₁HSpaceAssoc G using (η; H-⊙EM₁; H-⊙EM₁-assoc; H-EM₁-assoc-coh-unit-l-r-pentagon)
      open import homotopy.Pi2HSuspCompose H-⊙EM₁ H-⊙EM₁-assoc H-EM₁-assoc-coh-unit-l-r-pentagon
        using (comp)
      cancels-inverse : ∀ {i} {A : Type i} {x y : A}
        (p : x == y) (q : y == x) → p ∙ q == idp → ! p == q
      cancels-inverse p@idp q@.idp idp = idp

    to-alt-EM : ∀ n → EM G (S (S n)) ≃ Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ n (EM G 2))
    to-alt-EM n =
      (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) ⁻¹ ∘e
      coe-equiv (ap (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1))) ∘e
      coe-equiv (ap (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n)) ∘e
      coe-equiv (ap (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂))

  Susp-flip-EM-neg : ∀ n → EM-neg (S (S n)) ∼ Trunc-fmap Susp-flip
  Susp-flip-EM-neg n x =
    –>-is-inj (to-alt-EM n) (EM-neg (S (S n)) x) (Trunc-fmap Susp-flip x) $
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1)) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) $
     EM-neg (S (S n)) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1))) $
         ap (transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n)) $
         app= (! (transp-naturality (λ {k} → Trunc-fmap {n = k} (Susp^-fmap (S n) EM₁-neg))
                                    (+2+-comm 2 ⟨ n ⟩₋₂))) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1)) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     Trunc-fmap (Susp^-fmap (S n) EM₁-neg) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1))) $
         app= (! (transp-naturality (λ {l} → Trunc-fmap (Susp^-fmap l EM₁-neg))
                                    (+-comm 1 n))) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1)) $
     Trunc-fmap (Susp^-fmap (n + 1) EM₁-neg) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         app= (! (Trunc-fmap-coe (! (Susp^-+ n 1)))) $
         Trunc-fmap (Susp^-fmap (n + 1) EM₁-neg) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (! (Susp^-+ n 1))) $
     Trunc-fmap (Susp^-fmap (n + 1) EM₁-neg) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         Trunc-fmap-∘ (coe (! (Susp^-+ n 1))) (Susp^-fmap (n + 1) EM₁-neg) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (! (Susp^-+ n 1)) ∘ Susp^-fmap (n + 1) EM₁-neg) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         app= (ap Trunc-fmap (! (λ= (Susp^-+-natural' n 1 EM₁-neg)))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n (Susp-fmap EM₁-neg) ∘ coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ! $ Trunc-fmap-∘ (Susp^-fmap n (Susp-fmap EM₁-neg)) (coe (! (Susp^-+ n 1))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n (Susp-fmap EM₁-neg)) $
     Trunc-fmap (coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ Susp^-Trunc-equiv-natural' (Susp-fmap EM₁-neg) 2 n $
         Trunc-fmap (coe (! (Susp^-+ n 1))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (Trunc-fmap (Susp^-fmap n (EM-neg 2)) $
     <– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ app= (ap (Trunc-fmap ∘ Susp^-fmap n) (λ= Susp-flip-EM₁-neg)) $
         <– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
         Trunc-fmap (coe (! (Susp^-+ n 1))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (Trunc-fmap (Susp^-fmap n (Trunc-fmap Susp-flip)) $
     <– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ! $ Susp^-Trunc-equiv-natural' Susp-flip 2 n $
         Trunc-fmap (coe (! (Susp^-+ n 1))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n Susp-flip) $
     Trunc-fmap (coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         Trunc-fmap-∘ (Susp^-fmap n Susp-flip) (coe (! (Susp^-+ n 1))) $
         transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1))) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (Trunc-fmap (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1)))) $
         app= (ap coe (ap-∘ (Trunc (⟨ n ⟩₋₂ +2+ 2)) (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1))) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n)) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (Trunc-fmap (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1)))) $
         ! $ app= (Trunc-fmap-coe (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1))) $
     Trunc-fmap (coe (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         Trunc-fmap-∘ (Susp^-fmap n Susp-flip ∘ coe (! (Susp^-+ n 1)))
                      (coe (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (Susp^-fmap n Susp-flip ∘
                 coe (! (Susp^-+ n 1)) ∘
                 coe (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         app= (ap Trunc-fmap $ λ= $ λ y →
           (Susp^-fmap n Susp-flip $
            coe (! (Susp^-+ n 1)) $
            coe (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n)) y)
             =⟨ ap (Susp^-fmap n Susp-flip) $
                ! $ coe-∙ (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n)) (! (Susp^-+ n 1)) y ⟩
           (Susp^-fmap n Susp-flip $
            coe (Susp^-comm 1 n) y)
             =⟨ Susp^-comm-flip 0 n (EM₁ G.grp) y ⟩
           (coe (Susp^-comm 1 n) $
            Susp-flip y) =∎) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (Susp^-comm 1 n) ∘ Susp-flip) $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ! $ Trunc-fmap-∘ (coe (Susp^-comm 1 n)) (Susp-flip) $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     Trunc-fmap (coe (Susp^-comm 1 n)) $
     Trunc-fmap Susp-flip $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         app= (Trunc-fmap-coe (Susp^-comm 1 n)) $
         Trunc-fmap Susp-flip $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (Susp^-comm 1 n) $
     Trunc-fmap Susp-flip $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         transp-∙ {B = Trunc (⟨ n ⟩₋₂ +2+ 2)} (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n)) (! (Susp^-+ n 1)) $
         Trunc-fmap Susp-flip $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1)) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (ap (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n)) $
     Trunc-fmap Susp-flip $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1))) $
         app= (ap coe (∘-ap (Trunc (⟨ n ⟩₋₂ +2+ 2)) (λ l → Susp^ l (EM₁ G.grp)) (+-comm 1 n))) $
         Trunc-fmap Susp-flip $
         transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x ⟩
    (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n) $
     transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1)) $
     transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n) $
     Trunc-fmap Susp-flip $
     transport (λ k → Trunc k (Susp^ (S n) (EM₁ G.grp))) (+2+-comm 2 ⟨ n ⟩₋₂) x)
      =⟨ ap (<– (Susp^-Trunc-equiv (Susp (EM₁ G.grp)) 2 n)) $
         ap (transport (Trunc (⟨ n ⟩₋₂ +2+ 2)) (! (Susp^-+ n 1))) $
         ap (transport (λ l → Trunc (⟨ n ⟩₋₂ +2+ 2) (Susp^ l (EM₁ G.grp))) (+-comm 1 n)) $
         app= (transp-naturality (λ {k} → Trunc-fmap {n = k} Susp-flip) (+2+-comm 2 ⟨ n ⟩₋₂)) x ⟩
    –> (to-alt-EM n) (Trunc-fmap Susp-flip x) =∎

module _ {i} (G : AbGroup i) where

  private
    module G = AbGroup G

  ⊙EM-fmap-idhom : ∀ (n : ℕ)
    → ⊙EM-fmap G G (idhom G.grp) n == ⊙idf (⊙EM G n)
  ⊙EM-fmap-idhom O =
    ⊙Ω-fmap (⊙EM₁-fmap (idhom G.grp))
      =⟨ ap ⊙Ω-fmap (⊙λ= (⊙EM₁-fmap-idhom G.grp)) ⟩
    ⊙Ω-fmap (⊙idf (⊙EM₁ G.grp))
      =⟨ ⊙Ω-fmap-idf ⟩
    ⊙idf _ =∎
  ⊙EM-fmap-idhom (S n) =
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙EM₁-fmap (idhom G.grp)))
      =⟨ ap (⊙Trunc-fmap ∘ ⊙Susp^-fmap n) (⊙λ= (⊙EM₁-fmap-idhom G.grp)) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙idf (⊙EM₁ G.grp)))
      =⟨ ap ⊙Trunc-fmap (⊙Susp^-fmap-idf n (⊙EM₁ G.grp)) ⟩
    ⊙Trunc-fmap (⊙idf (⊙Susp^ n (⊙EM₁ G.grp)))
      =⟨ ⊙λ= ⊙Trunc-fmap-idf ⟩
    ⊙idf _ =∎

  EM-fmap-idhom : ∀ (n : ℕ)
    → EM-fmap G G (idhom G.grp) n == idf (EM G n)
  EM-fmap-idhom n = ap fst (⊙EM-fmap-idhom n)

transport-EM : ∀ {i} {G H : AbGroup i}
  (p : G == H) (n : ℕ)
  → transport (λ K → EM K n) p == EM-fmap G H (coeᴬᴳ p) n
transport-EM {G = G} idp n = ! $
  EM-fmap G G (coeᴳ idp) n
    =⟨ ap (λ φ → EM-fmap G G φ n) (coeᴳ-idp (AbGroup.grp G)) ⟩
  EM-fmap G G (idhom (AbGroup.grp G)) n
    =⟨ EM-fmap-idhom G n ⟩
  idf (EM G n) =∎

transport-EM-uaᴬᴳ : ∀ {i} (G H : AbGroup i)
  (iso : G ≃ᴬᴳ H) (n : ℕ)
  → transport (λ K → EM K n) (uaᴬᴳ G H iso) == EM-fmap G H (–>ᴳ iso) n
transport-EM-uaᴬᴳ G H iso n =
  transport (λ K → EM K n) (uaᴬᴳ G H iso)
    =⟨ transport-EM (uaᴬᴳ G H iso) n ⟩
  EM-fmap G H (coeᴬᴳ (uaᴬᴳ G H iso)) n
    =⟨ ap (λ p → EM-fmap G H p n) (coeᴬᴳ-β G H iso) ⟩
  EM-fmap G H (–>ᴳ iso) n =∎
