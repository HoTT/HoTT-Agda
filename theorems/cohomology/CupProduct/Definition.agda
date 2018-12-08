{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.CupProduct.OnEM.InAllDegrees
open import cohomology.CupProduct.OnEM.CommutativityInAllDegrees
open import cohomology.EMModel
open import cohomology.Theory
open import groups.ToOmega
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLaneFunctor
open import homotopy.Freudenthal
open import homotopy.SuspensionLoopSpaceInverse

module cohomology.CupProduct.Definition {i} (X : Ptd i) where

private
  module M {k} (A : AbGroup k) = CohomologyTheory (EM-Cohomology A)
  open M

⊙×-diag : X ⊙→ X ⊙× X
⊙×-diag = (λ x → x , x) , idp

smin-map : ∀ {j k} {Y : Ptd j} {Z : Ptd k}
  → X ⊙→ Y
  → X ⊙→ Z
  → X ⊙→ Y ⊙× Z
smin-map f g = ⊙×-fmap f g ⊙∘ ⊙×-diag

smin-map-⊙×-swap : ∀ {j k} (Y : Ptd j) (Z : Ptd k)
  (f : X ⊙→ Y)
  (g : X ⊙→ Z)
  → ⊙×-swap ⊙∘ smin-map g f == smin-map f g
smin-map-⊙×-swap Y Z (_ , idp) (_ , idp) = idp

module _ (G : AbGroup i) (H : AbGroup i) where

  private
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G
  open EMExplicit

  ⊙Ω×-cp-seq : ∀ (m n : ℕ) → (⊙Ω (⊙EM G (S m)) ⊙× ⊙Ω (⊙EM H (S n))) ⊙–→ ⊙Ω (⊙EM G⊗H.abgroup (S (m + n)))
  ⊙Ω×-cp-seq m n =
    ⊙<– (spectrum G⊗H.abgroup (m + n)) ◃⊙∘
    ⊙×-cp G H m n ◃⊙∘
    ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf

  ⊙Ω×-cp : ∀ (m n : ℕ) → ⊙Ω (⊙EM G (S m)) ⊙× ⊙Ω (⊙EM H (S n)) ⊙→ ⊙Ω (⊙EM G⊗H.abgroup (S (m + n)))
  ⊙Ω×-cp m n = ⊙compose (⊙Ω×-cp-seq m n)

  _∪_  : ∀ {m n : ℕ} → CEl G (pos m) X → CEl H (pos n) X → CEl G⊗H.abgroup (pos (m + n)) X
  _∪_ {m} {n} = Trunc-fmap2 {n = 0} (λ s' t' → ⊙Ω×-cp m n ⊙∘ smin-map s' t')

module _ (G : AbGroup i) (H : AbGroup i) where

  private
    module G⊗H = TensorProduct G H
    module H⊗G = TensorProduct H G
  open EMExplicit

  abstract
    ⊙Ω×-cp-comm : ∀ (m n : ℕ)
      → ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
        ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ◃⊙∘
        ⊙Ω×-cp G H m n ◃⊙idf
        =⊙∘
        ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
        ⊙Ω×-cp H G n m ◃⊙∘
        ⊙×-swap ◃⊙idf
    ⊙Ω×-cp-comm m n =
      ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
      ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ◃⊙∘
      ⊙Ω×-cp G H m n ◃⊙idf
        =⊙∘⟨ 2 & 1 & ⊙expand (⊙Ω×-cp-seq G H m n) ⟩
      ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
      ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ◃⊙∘
      ⊙<– (spectrum G⊗H.abgroup (m + n)) ◃⊙∘
      ⊙×-cp G H m n ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙<–-spectrum-natural G⊗H.abgroup H⊗G.abgroup G⊗H.swap (m + n) ⟩
      ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
      ⊙<– (spectrum H⊗G.abgroup (m + n)) ◃⊙∘
      ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (m + n) ◃⊙∘
      ⊙×-cp G H m n ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘⟨ 0 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
               (+-comm m n)
               (λ k → ⊙<– (spectrum H⊗G.abgroup k)) ⟩
      ⊙<– (spectrum H⊗G.abgroup (n + m)) ◃⊙∘
      ⊙transport (λ k → ⊙EM H⊗G.abgroup k) (+-comm m n) ◃⊙∘
      ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (m + n) ◃⊙∘
      ⊙×-cp G H m n ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘⟨ 1 & 3 & ⊙×-cp-comm G H m n ⟩
      ⊙<– (spectrum H⊗G.abgroup (n + m)) ◃⊙∘
      ⊙cond-neg H⊗G.abgroup (n + m) (and (odd m) (odd n)) ◃⊙∘
      ⊙×-cp H G n m ◃⊙∘
      ⊙×-swap ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘⟨ 0 & 2 & ⊙transport-natural-=⊙∘
               (Bool-elim (inv-path H⊗G.abgroup) idp (and (odd m) (odd n)))
               (λ A → ⊙<– (spectrum A (n + m))) ⟩
      ⊙transport (λ A → ⊙Ω (⊙EM A (S (n + m)))) neg ◃⊙∘
      ⊙<– (spectrum H⊗G.abgroup (n + m)) ◃⊙∘
      ⊙×-cp H G n m ◃⊙∘
      ⊙×-swap ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘₁⟨ 0 & 1 &
              ⊙transport-⊙coe (λ A → ⊙Ω (⊙EM A (S (n + m)))) neg ∙
              ap ⊙coe (ap-∘ ⊙Ω (λ A → ⊙EM A (S (n + m))) neg) ∙
              ! (⊙transport-⊙coe ⊙Ω (ap (λ A → ⊙EM A (S (n + m))) neg)) ∙
              ⊙transport-⊙Ω (ap (λ A → ⊙EM A (S (n + m))) neg) ∙
              ap ⊙Ω-fmap (! (⊙transport-⊙coe (λ A → ⊙EM A (S (n + m))) neg)) ⟩
      ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
      ⊙<– (spectrum H⊗G.abgroup (n + m)) ◃⊙∘
      ⊙×-cp H G n m ◃⊙∘
      ⊙×-swap ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ◃⊙idf
        =⊙∘⟨ 3 & 2 & =⊙∘-in {gs = ⊙×-fmap (⊙–> (spectrum H n)) (⊙–> (spectrum G m)) ◃⊙∘
                                  ⊙×-swap ◃⊙idf} $
                     ! $ ⊙λ= $ ⊙×-swap-natural (⊙–> (spectrum G m)) (⊙–> (spectrum H n)) ⟩
      ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
      ⊙<– (spectrum H⊗G.abgroup (n + m)) ◃⊙∘
      ⊙×-cp H G n m ◃⊙∘
      ⊙×-fmap (⊙–> (spectrum H n)) (⊙–> (spectrum G m)) ◃⊙∘
      ⊙×-swap ◃⊙idf
        =⊙∘⟨ 1 & 3 & ⊙contract ⟩
      ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
      ⊙Ω×-cp H G n m ◃⊙∘
      ⊙×-swap ◃⊙idf ∎⊙∘
      where
      neg : H⊗G.abgroup == H⊗G.abgroup
      neg = Bool-elim (inv-path H⊗G.abgroup) idp (and (odd m) (odd n))

  ∪-swap : ∀ (m n : ℕ)
    → CEl G⊗H.abgroup (pos (m + n)) X → CEl H⊗G.abgroup (pos (n + m)) X
  ∪-swap m n =
    transport (λ k → CEl H⊗G.abgroup (pos k) X) (+-comm m n) ∘
    EM-coeff-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap X (pos (m + n))

  maybe-inv : ∀ (n : ℤ) → Bool → CEl H⊗G.abgroup n X → CEl H⊗G.abgroup n X
  maybe-inv n = Bool-rec (Group.inv (C H⊗G.abgroup n X)) (idf _)

  private
    _G∪H_ = _∪_ G H
    _H∪G_ = _∪_ H G

  ∪-comm : ∀ {m n : ℕ}
    (s : CEl G (pos m) X)
    (t : CEl H (pos n) X)
    → ∪-swap m n (s G∪H t) ==
      maybe-inv (pos (n + m)) (and (odd m) (odd n)) (t H∪G s)
  ∪-comm {m} {n} =
    Trunc-elim {{λ s → Π-level (λ t → =-preserves-level Trunc-level)}} $ λ s' →
    Trunc-elim {{λ t → =-preserves-level Trunc-level}} $ λ t' →
    transport (λ k → CEl H⊗G.abgroup (pos k) X) (+-comm m n)
    [ ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ⊙∘
      ⊙Ω×-cp G H m n ⊙∘
      smin-map s' t' ]
      =⟨ app= step₁
         [ ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ⊙∘
           ⊙Ω×-cp G H m n ⊙∘
           smin-map s' t' ] ⟩
    [ ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ⊙∘
      ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ⊙∘
      ⊙Ω×-cp G H m n ⊙∘
      smin-map s' t' ]
      =⟨ ap [_] (=⊙∘-out (step₂ s' t')) ⟩
    Trunc-fmap (⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ⊙∘_)
    [ ⊙Ω×-cp H G n m ⊙∘ smin-map t' s' ]
      =⟨ app= (step₃ (n + m) (and (odd m) (odd n))) [ ⊙Ω×-cp H G n m ⊙∘ smin-map t' s' ] ⟩
    maybe-inv (pos (n + m)) (and (odd m) (odd n))
    [ ⊙Ω×-cp H G n m ⊙∘ smin-map t' s' ] =∎
    where
    step₁ : transport (λ k → CEl H⊗G.abgroup (pos k) X) (+-comm m n) ==
            Trunc-fmap (⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ⊙∘_)
    step₁ =
      transport (λ k → CEl H⊗G.abgroup (pos k) X) (+-comm m n)
        =⟨ ap coe (ap-∘ (Trunc 0) (λ k → X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)) ⟩
      transport (Trunc 0) (ap (λ k → X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n))
        =⟨ transport-Trunc (ap (λ k → X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)) ⟩
      Trunc-fmap (transport (λ k → X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n))
        =⟨ ap (Trunc-fmap ∘ coe) (ap-∘ (X ⊙→_) (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)) ⟩
      Trunc-fmap (transport (X ⊙→_) (ap (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)))
        =⟨ ap Trunc-fmap $ λ= $ transport-post⊙∘ X (ap (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)) ⟩
      Trunc-fmap (⊙coe (ap (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n)) ⊙∘_)
        =⟨ ap (λ g → Trunc-fmap (g ⊙∘_)) $
           ! $ ⊙transport-⊙coe (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ⟩
      Trunc-fmap (⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ⊙∘_) =∎
    step₂ : ∀ (s' : X ⊙→ ⊙Ω (⊙EM G (S m))) (t' : X ⊙→ ⊙Ω (⊙EM H (S n)))
      → ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
        ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ◃⊙∘
        ⊙Ω×-cp G H m n ◃⊙∘
        smin-map s' t' ◃⊙idf
        =⊙∘
        ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
        ⊙Ω×-cp H G n m ◃⊙∘
        smin-map t' s' ◃⊙idf
    step₂ s' t' =
      ⊙transport (λ k → ⊙Ω (⊙EM H⊗G.abgroup (S k))) (+-comm m n) ◃⊙∘
      ⊙Ω-fmap (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S (m + n))) ◃⊙∘
      ⊙Ω×-cp G H m n ◃⊙∘
      smin-map s' t' ◃⊙idf
        =⊙∘⟨ 0 & 3 & ⊙Ω×-cp-comm m n ⟩
      ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
      ⊙Ω×-cp H G n m ◃⊙∘
      ⊙×-swap ◃⊙∘
      smin-map s' t' ◃⊙idf
        =⊙∘⟨ 2 & 2 & =⊙∘-in {gs = smin-map t' s' ◃⊙idf} $
             smin-map-⊙×-swap (⊙Ω (⊙EM H (S n))) (⊙Ω (⊙EM G (S m))) t' s' ⟩
      ⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S (n + m)) (and (odd m) (odd n))) ◃⊙∘
      ⊙Ω×-cp H G n m ◃⊙∘
      smin-map t' s' ◃⊙idf ∎⊙∘
    step₃ : ∀ (k : ℕ) (b : Bool) →
      Trunc-fmap (⊙Ω-fmap (⊙cond-neg H⊗G.abgroup (S k) b) ⊙∘_) ==
      maybe-inv (pos k) b
    step₃ k false =
      Trunc-fmap (⊙Ω-fmap (⊙idf (⊙EM H⊗G.abgroup (S k))) ⊙∘_)
        =⟨ ap (λ g → Trunc-fmap (g ⊙∘_)) ⊙Ω-fmap-idf ⟩
      Trunc-fmap (⊙idf (⊙Ω (⊙EM H⊗G.abgroup (S k))) ⊙∘_)
        =⟨ ap Trunc-fmap (λ= (⊙λ= ∘ ⊙∘-unit-l)) ⟩
      Trunc-fmap (idf (X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k))))
        =⟨ λ= Trunc-fmap-idf ⟩
      idf (Trunc 0 (X ⊙→ ⊙Ω (⊙EM H⊗G.abgroup (S k)))) =∎
    step₃ k true =
      Trunc-fmap (⊙Ω-fmap (⊙transport (λ A → ⊙EM A (S k)) (inv-path H⊗G.abgroup)) ⊙∘_)
        =⟨ ap (λ g → Trunc-fmap (g ⊙∘_)) (=⊙∘-out (step₃' k)) ⟩
      Trunc-fmap (⊙Ω-! ⊙∘_)
        =⟨ ap Trunc-fmap {x = ⊙Ω-! ⊙∘_} {y = GroupStructure.inv (⊙→Ω-group-structure X (⊙EM H⊗G.abgroup (S k)))} $
           λ= (λ f → ⊙λ=' (λ x → idp) (∙-unit-r (ap ! (snd f)))) ⟩
      Group.inv (C H⊗G.abgroup (pos k) X) =∎
      where
      step₃' : ∀ (k : ℕ)
        → ⊙Ω-fmap (⊙transport (λ A → ⊙EM A (S k)) (inv-path H⊗G.abgroup)) ◃⊙idf
          =⊙∘
          ⊙Ω-! ◃⊙idf
      step₃' 0 =
        ⊙Ω-fmap (⊙transport (λ A → ⊙EM A 1) (inv-path H⊗G.abgroup)) ◃⊙idf
          =⊙∘₁⟨ ap ⊙Ω-fmap (⊙transport-⊙EM-uaᴬᴳ H⊗G.abgroup H⊗G.abgroup (inv-iso H⊗G.abgroup) 1) ⟩
        ⊙Ω-fmap (⊙Trunc-fmap (⊙EM₁-fmap (inv-hom H⊗G.abgroup))) ◃⊙idf
          =⊙∘⟨ 0 & 0 & !⊙∘ $ ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙Ω-fmap (⊙Trunc-fmap (⊙EM₁-fmap (inv-hom H⊗G.abgroup))) ◃⊙idf
          =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ 0 (⊙EM₁-fmap (inv-hom H⊗G.abgroup)) ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙Trunc-fmap (⊙Ω-fmap (⊙EM₁-fmap (inv-hom H⊗G.abgroup))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙idf
          =⊙∘₁⟨ 1 & 1 & ap ⊙Trunc-fmap $ ⊙Ω-fmap-⊙EM₁-neg H⊗G.abgroup ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙Trunc-fmap ⊙Ω-! ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙idf
          =⊙∘⟨ 1 & 2 & =⊙∘-in
               {gs = ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
                     ⊙Ω-! ◃⊙idf} $
               ! $ ⊙λ=' –>-=ₜ-equiv-pres-! idp ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ◃⊙∘
        ⊙Ω-! ◃⊙idf
          =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ (AbGroup.grp H⊗G.abgroup))) ⟩
        ⊙Ω-! ◃⊙idf ∎⊙∘
      step₃' (S k) =
        ⊙Ω-fmap (⊙transport (λ A → ⊙EM A (S (S k))) (inv-path H⊗G.abgroup)) ◃⊙idf
          =⊙∘₁⟨ ap ⊙Ω-fmap (⊙transport-⊙EM-uaᴬᴳ H⊗G.abgroup H⊗G.abgroup (inv-iso H⊗G.abgroup) (S (S k))) ⟩
        ⊙Ω-fmap (⊙EM-fmap H⊗G.abgroup H⊗G.abgroup (inv-hom H⊗G.abgroup) (S (S k))) ◃⊙idf
          =⊙∘₁⟨ ap ⊙Ω-fmap (⊙EM-neg=⊙Trunc-fmap-⊙Susp-flip H⊗G.abgroup k) ⟩
        ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ (AbGroup.grp H⊗G.abgroup))))) ◃⊙idf
          =⊙∘⟨ 0 & 0 & !⊙∘ $
               ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ (AbGroup.grp H⊗G.abgroup))))) ◃⊙idf
          =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ ⟨ S k ⟩
                 (⊙Susp-flip (⊙Susp^ k (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ (AbGroup.grp H⊗G.abgroup))))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙idf
          =⊙∘₁⟨ 1 & 1 & ! $ ⊙Ω-!-⊙Susp-flip
                  (⊙Susp^ k (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))
                  ⟨ S k ⟩
                  (Spectrum.Trunc-fmap-σloop-is-equiv H⊗G.abgroup k) ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙Trunc-fmap ⊙Ω-! ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙idf
          =⊙∘⟨ 1 & 2 & =⊙∘-in
               {gs = ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
                     ⊙Ω-! ◃⊙idf} $
               ! $ ⊙λ=' –>-=ₜ-equiv-pres-! idp ⟩
        ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ◃⊙∘
        ⊙Ω-! ◃⊙idf
          =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ (AbGroup.grp H⊗G.abgroup)))) ⟩
        ⊙Ω-! ◃⊙idf ∎⊙∘
