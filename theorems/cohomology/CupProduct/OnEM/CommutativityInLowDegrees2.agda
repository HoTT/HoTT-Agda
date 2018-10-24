{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLaneFunctor
open import cohomology.CupProduct.OnEM.CommutativityInLowDegrees

module cohomology.CupProduct.OnEM.CommutativityInLowDegrees2 {i} {j} (G : AbGroup i) (H : AbGroup j) where

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
  module H⊗G = TensorProduct H G
  module GHc = CP₁₁-comm G H
  module HGc = CP₁₁-comm H G

import cohomology.CupProduct.OnEM.InLowDegrees2 G H as GH
import cohomology.CupProduct.OnEM.InLowDegrees2 H G as HG

private
  ∧-cp₁₁-comm-smgluel : ∀ (x : EM₁ G.grp)
    → Square (GHc.CP₁₁Comm.f x embase)
             (ap GH.∧-cp₁₁ (smgluel x))
             (ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluel x))
             idp
  ∧-cp₁₁-comm-smgluel x =
    GH.∧-cp₁₁-Rec.smgluel-β x ∙v⊡
    lt-square (GH.cp₁₁-embase-r x) ⊡v∙
    ! bottom-path
    where
    bottom-path : ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluel x) == idp
    bottom-path =
      ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluel x)
        =⟨ ap-∘ (GHc.− ∘ HG.∧-cp₁₁) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluel x) ⟩
      ap (GHc.− ∘ HG.∧-cp₁₁) (ap (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluel x))
        =⟨ ap (ap (GHc.− ∘ HG.∧-cp₁₁)) (SmashSwap.smgluel-β (⊙EM₁ G.grp) (⊙EM₁ H.grp) x) ⟩
      ap (GHc.− ∘ HG.∧-cp₁₁) (∧-norm-r x)
        =⟨ ap-∘ GHc.− HG.∧-cp₁₁ (∧-norm-r x) ⟩
      ap GHc.− (ap HG.∧-cp₁₁ (∧-norm-r x))
        =⟨ ap (ap GHc.−) (HG.∧-cp₁₁-Rec.∧-norm-r-β x) ⟩
      idp =∎

  cp₁₁-comm-sym : ∀ (y : EM₁ H.grp)
    → ! (GHc.CP₁₁Comm.f embase y) == ap GHc.− (HGc.CP₁₁Comm.f y embase)
  cp₁₁-comm-sym =
    EM₁-set-elim
      {P = λ y → ! (GHc.CP₁₁Comm.f embase y) == ap GHc.− (HGc.CP₁₁Comm.f y embase)}
      {{λ y → has-level-apply (has-level-apply (Trunc-level {n = 2}) _ _) _ _}}
      idp $ λ h →
    ↓-=-in $
    idp ◃ apd (λ y → ap GHc.− (HGc.CP₁₁Comm.f y embase)) (emloop h)
      =⟨ idp◃ (apd (λ y → ap GHc.− (HGc.CP₁₁Comm.f y embase)) (emloop h)) ⟩
    apd (λ y → ap GHc.− (HGc.CP₁₁Comm.f y embase)) (emloop h)
      =⟨ apd-∘' (ap GHc.−) (λ y → HGc.CP₁₁Comm.f y embase) (emloop h) ⟩
    ap↓ (ap GHc.−) (apd (λ y → HGc.CP₁₁Comm.f y embase) (emloop h))
      =⟨ ap (ap↓ (ap GHc.−)) (HGc.CP₁₁Comm.emloop-embase-β h) ⟩
    ap↓ (ap GHc.−) (↓-='-from-square (HGc.comm-emloop-embase h))
      =⟨ ↓-='-from-square-post-∘ {h = GHc.−} (HGc.comm-emloop-embase h) ⟩
    ↓-='-from-square (ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
                      ap-square GHc.− (HGc.comm-emloop-embase h) ⊡v∙
                      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h))
      =⟨ ap ↓-='-from-square (square-path h) ⟩
    ↓-='-from-square (!□v (GHc.comm-embase-emloop h))
      =⟨ ! (↓-='-from-square-! (GHc.comm-embase-emloop h)) ⟩
    ap↓ ! (↓-='-from-square (GHc.comm-embase-emloop h))
      =⟨ ap (ap↓ !) (! (GHc.CP₁₁Comm.embase-emloop-β h)) ⟩
    ap↓ ! (apd (λ y → GHc.CP₁₁Comm.f embase y) (emloop h))
      =⟨ ! (apd-∘' ! (λ y → GHc.CP₁₁Comm.f embase y) (emloop h)) ⟩
    apd (λ y → ! (GHc.CP₁₁Comm.f embase y)) (emloop h)
      =⟨ ! (▹idp (apd (λ y → ! (GHc.CP₁₁Comm.f embase y)) (emloop h))) ⟩
    apd (λ y → ! (GHc.CP₁₁Comm.f embase y)) (emloop h) ▹ idp =∎
    where
    =ₛ-path : ∀ (h : H.El) →
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ap (ap GHc.−) (HGc.comm-emloop-embase' h) ◃∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h) ◃∎
      =ₛ
      ! (GHc.comm-embase-emloop' h) ◃∎
    =ₛ-path h = !ₛ $
      ! (GHc.comm-embase-emloop' h) ◃∎
        =ₛ⟨ !-∙-seq (GHc.comm-embase-emloop-seq h) ⟩
      ! (∘-ap GHc.− (λ y → HG.cp₁₁ y embase) (emloop h)) ◃∙
      ! (! (ap (ap GHc.−) (HG.ap-cp₁₁-embase h))) ◃∙
      ! (ap-cst [ north ] (emloop h)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (! (!ap-∘=∘-ap GHc.− (λ y → HG.cp₁₁ y embase) (emloop h))) ∙
                     !-! (ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h)) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ! (! (ap (ap GHc.−) (HG.ap-cp₁₁-embase h))) ◃∙
      ! (ap-cst [ north ] (emloop h)) ◃∎
        =ₛ₁⟨ 1 & 1 & !-! (ap (ap GHc.−) (HG.ap-cp₁₁-embase h)) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ap (ap GHc.−) (HG.ap-cp₁₁-embase h) ◃∙
      ! (ap-cst [ north ]₂ (emloop h)) ◃∎
        =ₛ⟨ 2 & 2 & !ₛ $
            post-rotate-in {p = _ ◃∙ _ ◃∎} $
            pre-rotate'-in $
            ap-∘-cst-coh GHc.− [ north ]₂ (emloop h) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ap (ap GHc.−) (HG.ap-cp₁₁-embase h) ◃∙
      ! (ap (ap GHc.−) (ap-cst [ north ] (emloop h))) ◃∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h) ◃∎
        =ₛ₁⟨ 2 & 1 & !-ap (ap GHc.−) (ap-cst [ north ]₂ (emloop h)) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ap (ap GHc.−) (HG.ap-cp₁₁-embase h) ◃∙
      ap (ap GHc.−) (! (ap-cst [ north ]₂ (emloop h))) ◃∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h) ◃∎
        =ₛ⟨ 1 & 2 & ∙-ap-seq (ap GHc.−) (HGc.comm-emloop-embase-seq h) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ◃∙
      ap (ap GHc.−) (HGc.comm-emloop-embase' h) ◃∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h) ◃∎ ∎ₛ
    square-path : ∀ (h : H.El) →
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
      ap-square GHc.− (HGc.comm-emloop-embase h) ⊡v∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)
      ==
      !□v (GHc.comm-embase-emloop h)
    square-path h =
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
      ap-square GHc.− (HGc.comm-emloop-embase h) ⊡v∙
      ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)
        =⟨ ap (λ u → ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
                     u ⊡v∙
                     ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)) $
           ap-vert-degen-square GHc.− (HGc.comm-emloop-embase' h) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
      vert-degen-square (ap (ap GHc.−) (HGc.comm-emloop-embase' h))
      ⊡v∙ ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)
        =⟨ ap (ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡_) $
           vert-degen-square-⊡v∙ (ap (ap GHc.−) (HGc.comm-emloop-embase' h))
                                 (∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)) ⟩
      ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙v⊡
      vert-degen-square (ap (ap GHc.−) (HGc.comm-emloop-embase' h) ∙
                         ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h))
        =⟨ vert-degen-square-∙v⊡
             (ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h))
             (ap (ap GHc.−) (HGc.comm-emloop-embase' h) ∙
              ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h)) ⟩
      vert-degen-square (ap-∘ GHc.− (λ y → HG.cp₁₁ y embase) (emloop h) ∙
                         ap (ap GHc.−) (HGc.comm-emloop-embase' h) ∙
                         ∘-ap GHc.− (λ y → HGc.− (GH.cp₁₁ embase y)) (emloop h))
        =⟨ ap vert-degen-square (=ₛ-out (=ₛ-path h)) ⟩
      vert-degen-square (! (GHc.comm-embase-emloop' h))
        =⟨ ! (!□v-vert-degen-square (GHc.comm-embase-emloop' h)) ⟩
      !□v (GHc.comm-embase-emloop h) =∎

  ∧-cp₁₁-comm-smgluer : ∀ (y : EM₁ H.grp)
    → Square (GHc.CP₁₁Comm.f embase y)
             (ap GH.∧-cp₁₁ (smgluer y))
             (ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluer y))
             idp
  ∧-cp₁₁-comm-smgluer y =
    GH.∧-cp₁₁-Rec.smgluer-β y ∙v⊡
    ! (!-! (GHc.CP₁₁Comm.f embase y)) ∙h⊡
    ap ! (cp₁₁-comm-sym y) ∙h⊡
    bl-square (ap GHc.− (HG.cp₁₁-embase-r y)) ⊡v∙
    ! bottom-path
    where
    bottom-path : ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluer y) == ap GHc.− (HG.cp₁₁-embase-r y)
    bottom-path =
      ap (GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluer y)
        =⟨ ap-∘ (GHc.− ∘ HG.∧-cp₁₁) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluer y) ⟩
      ap (GHc.− ∘ HG.∧-cp₁₁) (ap (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) (smgluer y))
        =⟨ ap (ap (GHc.− ∘ HG.∧-cp₁₁)) (SmashSwap.smgluer-β (⊙EM₁ G.grp) (⊙EM₁ H.grp) y) ⟩
      ap (GHc.− ∘ HG.∧-cp₁₁) (∧-norm-l y)
        =⟨ ap-∘ GHc.− HG.∧-cp₁₁ (∧-norm-l y) ⟩
      ap GHc.− (ap HG.∧-cp₁₁ (∧-norm-l y))
        =⟨ ap (ap GHc.−) (HG.∧-cp₁₁-Rec.∧-norm-l-β y) ⟩
      ap GHc.− (HG.cp₁₁-embase-r y ∙ idp)
        =⟨ ap (ap GHc.−) (∙-unit-r (HG.cp₁₁-embase-r y)) ⟩
      ap GHc.− (HG.cp₁₁-embase-r y) =∎

private
  ∧-cp₁₁-comm' : GH.∧-cp₁₁ ∼ GHc.− ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)
  ∧-cp₁₁-comm' =
    Smash-elim
      {P = λ s → GH.∧-cp₁₁ s == GHc.− (HG.∧-cp₁₁ (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s))}
      GHc.CP₁₁Comm.f
      idp
      idp
      (λ x → ↓-='-from-square (∧-cp₁₁-comm-smgluel x))
      (λ y → ↓-='-from-square (∧-cp₁₁-comm-smgluer y))


∧-cp₁₁-comm : EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2 ∘ GH.∧-cp₁₁
            ∼ EM-neg H⊗G.abgroup 2 ∘ HG.∧-cp₁₁ ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)
∧-cp₁₁-comm s =
  (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2 $
   GH.∧-cp₁₁ s)
    =⟨ ap (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2) $
       ∧-cp₁₁-comm' s ⟩
  (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2 $
   GHc.− $
   HG.∧-cp₁₁ $
   ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s)
    =⟨ ap (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2) $
       app= minus $
       HG.∧-cp₁₁ $
       ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s ⟩
  (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2 $
   EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap 2 $
   EM-neg H⊗G.abgroup 2 $
   HG.∧-cp₁₁ $
   ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s)
    =⟨ ! $ app= (EM-fmap-∘ H⊗G.abgroup G⊗H.abgroup H⊗G.abgroup G⊗H.swap H⊗G.swap 2) $
       EM-neg H⊗G.abgroup 2 $
       HG.∧-cp₁₁ $
       ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s ⟩
  (EM-fmap H⊗G.abgroup H⊗G.abgroup (G⊗H.swap ∘ᴳ H⊗G.swap) 2 $
   EM-neg H⊗G.abgroup 2 $
   HG.∧-cp₁₁ $
   ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s)
    =⟨ app= (ap (λ f → EM-fmap H⊗G.abgroup H⊗G.abgroup f 2) H⊗G.swap-swap-idhom) $
       EM-neg H⊗G.abgroup 2 $
       HG.∧-cp₁₁ $
       ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s ⟩
  (EM-fmap H⊗G.abgroup H⊗G.abgroup (idhom H⊗G.grp) 2 $
   EM-neg H⊗G.abgroup 2 $
   HG.∧-cp₁₁ $
   ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s)
    =⟨ app= (EM-fmap-idhom H⊗G.abgroup 2) $
       EM-neg H⊗G.abgroup 2 $
       HG.∧-cp₁₁ $
       ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s ⟩
  (EM-neg H⊗G.abgroup 2 $
   HG.∧-cp₁₁ $
   ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) s) =∎
  where
  minus : GHc.− == EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap 2 ∘ EM-neg H⊗G.abgroup 2
  minus =
    Trunc-fmap (Susp-fmap (EM₁-fmap (inv-hom G⊗H.abgroup) ∘ EM₁-fmap H⊗G.swap))
      =⟨ ap (Trunc-fmap ∘ Susp-fmap) (! (λ= (EM₁-fmap-∘ (inv-hom G⊗H.abgroup) H⊗G.swap))) ⟩
    EM-fmap H⊗G.abgroup G⊗H.abgroup (inv-hom G⊗H.abgroup ∘ᴳ H⊗G.swap) 2
      =⟨ ap (λ φ → EM-fmap H⊗G.abgroup G⊗H.abgroup φ 2)
            (! (inv-hom-natural H⊗G.abgroup G⊗H.abgroup H⊗G.swap))  ⟩
    EM-fmap H⊗G.abgroup G⊗H.abgroup (H⊗G.swap ∘ᴳ inv-hom H⊗G.abgroup) 2
      =⟨ EM-fmap-∘ H⊗G.abgroup H⊗G.abgroup G⊗H.abgroup (H⊗G.swap) (inv-hom H⊗G.abgroup) 2 ⟩
    EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap 2 ∘ EM-neg H⊗G.abgroup 2 =∎
