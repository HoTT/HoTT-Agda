{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.SmashFmapConn
open import homotopy.SuspSmash2

module cohomology.CupProduct.OnEM.Higher {i} {j} (G : AbGroup i) (H : AbGroup j) where

open import cohomology.CupProduct.OnEM.Definition G H

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
open EMExplicit

cp₁₁-embase-r : (x : EM₁ G.grp) → cp₁₁ x embase == [ north ]₂
cp₁₁-embase-r = M.f
  where
  module M =
    EM₁Level₂PathConstElim G.grp {C = EM G⊗H.abgroup 2} {{Trunc-level {n = 2}}}
      (λ x → cp₁₁ x embase) [ north ]₂
      idp
      (λ g → vert-degen-square (ap-cp₁₁-embase g))
      (λ g₁ g₂ →
        vert-degen-square (ap-cp₁₁-embase (G.comp g₁ g₂))
          =⟨ ap vert-degen-square $
             =ₛ-out (ap-cp₁₁-embase-coh g₁ g₂) ∙
             ! (∙-assoc (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂))
                        (ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂))
                        (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))) ⟩
        vert-degen-square
          ((ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
            ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙
           ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))
          =⟨ ! $ vert-degen-square-∙v⊡
                   (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
                    ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂))
                   (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂)) ⟩
        (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
         ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡
        vert-degen-square (ap2 _∙_ (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂))
          =⟨ ap ((ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
                  ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡_) $
             ! (vert-degen-square-⊡h (ap-cp₁₁-embase g₁) (ap-cp₁₁-embase g₂)) ⟩
        (ap (ap (λ x → cp₁₁ x embase)) (emloop-comp g₁ g₂) ∙
         ap-∙ (λ x → cp₁₁ x embase) (emloop g₁) (emloop g₂)) ∙v⊡
        (vert-degen-square (ap-cp₁₁-embase g₁) ⊡h
         vert-degen-square (ap-cp₁₁-embase g₂)) =∎)

module ∧-cp₁₁-Rec =
  SmashRec {X = ⊙EM₁ G.grp} {Y = ⊙EM₁ H.grp} {C = EM G⊗H.abgroup 2}
           cp₁₁
           [ north ]₂ [ north ]₂
           cp₁₁-embase-r
           (λ y → idp)

∧-cp₁₁ : ⊙EM₁ G.grp ∧ ⊙EM₁ H.grp → EM G⊗H.abgroup 2
∧-cp₁₁ = ∧-cp₁₁-Rec.f

⊙∧-cp₁₁ : ⊙EM₁ G.grp ⊙∧ ⊙EM₁ H.grp ⊙→ ⊙EM G⊗H.abgroup 2
⊙∧-cp₁₁ = ∧-cp₁₁-Rec.f , idp

EM2-Susp : ∀ (k : ℕ)
  → Susp^ k (EM G⊗H.abgroup 2)
  → EM G⊗H.abgroup (S (S k))
EM2-Susp k =
  transport (λ l → Trunc l (Susp^ (S k) (EM₁ G⊗H.grp))) (+2+-comm ⟨ k ⟩₋₂ 2) ∘
  Trunc-fmap (<– (Susp^-Susp-split-iso k (EM₁ G⊗H.grp))) ∘
  Susp^-Trunc-swap (Susp (EM₁ G⊗H.grp)) k 2

cp' : ∀ (n m : ℕ)
  → ⊙Susp^ n (⊙EM₁ G.grp) ∧ ⊙Susp^ m (⊙EM₁ H.grp)
  → EM G⊗H.abgroup (S n + S m)
cp' n m =
  transport (EM G⊗H.abgroup) (! (+-βr (S n) m)) ∘
  EM2-Susp (n + m) ∘
  Susp^-fmap (n + m) ∧-cp₁₁ ∘
  Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) n m

smash-truncate : ∀ (n m : ℕ)
  → ⊙Susp^ n (⊙EM₁ G.grp) ∧ ⊙Susp^ m (⊙EM₁ H.grp)
  → ⊙EM G (S n) ∧ ⊙EM H (S m)
smash-truncate n m =
  ∧-fmap
    ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ G.grp)} , idp)
    ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ H.grp)} , idp)

smash-truncate-conn : ∀ (n m : ℕ)
  → has-conn-fibers ⟨ S n + S m ⟩ (smash-truncate n m)
smash-truncate-conn n m =
  transport (λ k → has-conn-fibers k (smash-truncate n m)) p $
  ∧-fmap-conn
    ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ G.grp)} , idp)
    ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ H.grp)} , idp)
    (EM-conn G n)
    (⊙Susp^-conn' m {{EM₁-conn}})
    (trunc-proj-conn (Susp^ n (EM₁ G.grp)) ⟨ S n ⟩)
    (trunc-proj-conn (Susp^ m (EM₁ H.grp)) ⟨ S m ⟩)
  where
  p₁ : ⟨ m ⟩₋₁ +2+ ⟨ S n ⟩ == ⟨ S n + S m ⟩
  p₁ =
    ⟨ m ⟩₋₁ +2+ ⟨ S n ⟩
      =⟨ ! (+-+2+ (S m) (S (S (S n)))) ⟩
    ⟨ m + S (S (S n)) ⟩₋₁
      =⟨ ap ⟨_⟩₋₁ (+-βr m (S (S n))) ⟩
    ⟨ m + S (S n) ⟩
      =⟨ ap ⟨_⟩ (+-βr m (S n)) ⟩
    ⟨ S m + S n ⟩
      =⟨ ap ⟨_⟩ (+-comm (S m) (S n)) ⟩
    ⟨ S n + S m ⟩ =∎
  p₂ : ⟨ n ⟩₋₁ +2+ ⟨ S m ⟩ == ⟨ S n + S m ⟩
  p₂ =
    ⟨ n ⟩₋₁ +2+ ⟨ S m ⟩
      =⟨ ! (+-+2+ (S n) (S (S (S m)))) ⟩
    ⟨ n + S (S (S m)) ⟩₋₁
      =⟨ ap ⟨_⟩₋₁ (+-βr n (S (S m))) ⟩
    ⟨ n + S (S m) ⟩
      =⟨ ap ⟨_⟩ (+-βr n (S m)) ⟩
    ⟨ S n + S m ⟩ =∎
  p : minT (⟨ m ⟩₋₁ +2+ ⟨ S n ⟩) (⟨ n ⟩₋₁ +2+ ⟨ S m ⟩) == ⟨ S n + S m ⟩
  p =
    minT (⟨ m ⟩₋₁ +2+ ⟨ S n ⟩) (⟨ n ⟩₋₁ +2+ ⟨ S m ⟩)
      =⟨ ap2 minT p₁ p₂ ⟩
    minT ⟨ S n + S m ⟩ ⟨ S n + S m ⟩
      =⟨ minT-out-l ≤T-refl ⟩
    ⟨ S n + S m ⟩ =∎

cp : ∀ (n m : ℕ)
  → ⊙EM G (S n) ∧ ⊙EM H (S m)
  → EM G⊗H.abgroup (S n + S m)
cp n m =
  conn-extend
    (smash-truncate-conn n m)
    (λ _ → EM G⊗H.abgroup (S n + S m) , EM-level G⊗H.abgroup (S n + S m))
    (cp' n m)
