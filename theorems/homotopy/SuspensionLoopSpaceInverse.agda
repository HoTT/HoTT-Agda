{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.SuspensionLoopSpaceInverse where

{- corollary about inversion in ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X))) -}
private
  custom-path-alg : ∀ {l} {A : Type l}
    {n s : A} (p q : n == s)
    → ! (p ∙ ! q) == ! (! q) ∙ (! p ∙ q) ∙' ! q
  custom-path-alg p q@idp = ap ! (∙-unit-r p) ∙ ! (∙-unit-r (! p))

  Ω-!-Susp-flip-seq : ∀ {i} (X : Ptd i) (x : de⊙ X)
    → ! (merid x ∙ ! (merid (pt X)))
      =-=
      Ω-fmap (⊙Susp-flip X) (σloop X x)
  Ω-!-Susp-flip-seq X x =
    ! (merid x ∙ ! (merid (pt X)))
      =⟪ custom-path-alg (merid x) (merid (pt X)) ⟫
    ! (! (merid (pt X))) ∙ (! (merid x) ∙ merid (pt X)) ∙' ! (merid (pt X))
      =⟪ ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
            (! (Susp-flip-σloop X x)) ⟫
    ! (! (merid (pt X))) ∙ ap Susp-flip (σloop X x) ∙' ! (merid (pt X))
      =⟪ ! (Ω-fmap-β (⊙Susp-flip X) (merid x ∙ ! (merid (pt X)))) ⟫
    Ω-fmap (⊙Susp-flip X) (σloop X x) ∎∎

  Ω-!-Susp-flip' : ∀ {i} (X : Ptd i)
    → Ω-! ∘ σloop X ∼ Ω-fmap (⊙Susp-flip X) ∘ σloop X
  Ω-!-Susp-flip' X x = ↯ (Ω-!-Susp-flip-seq X x)

  ⊙Ω-!-Susp-flip' : ∀ {i} (X : Ptd i)
    → ⊙Ω-! ◃⊙∘
      ⊙σloop X ◃⊙idf
      =⊙∘
      ⊙Ω-fmap (⊙Susp-flip X) ◃⊙∘
      ⊙σloop X ◃⊙idf
  ⊙Ω-!-Susp-flip' X = ⊙seq-λ= (Ω-!-Susp-flip' X) $ !ₛ $
    ↯ (Ω-!-Susp-flip-seq X (pt X)) ◃∙
    ap (Ω-fmap (⊙Susp-flip X)) (!-inv-r (merid (pt X))) ◃∙
    snd (⊙Ω-fmap (⊙Susp-flip X)) ◃∎
      =ₛ⟨ 0 & 1 & expand (Ω-!-Susp-flip-seq X (pt X)) ⟩
    custom-path-alg (merid (pt X)) (merid (pt X)) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (! (Susp-flip-σloop X (pt X))) ◃∙
    ! (Ω-fmap-β (⊙Susp-flip X) (merid (pt X) ∙ ! (merid (pt X)))) ◃∙
    ap (Ω-fmap (⊙Susp-flip X)) (!-inv-r (merid (pt X))) ◃∙
    snd (⊙Ω-fmap (⊙Susp-flip X)) ◃∎
      =ₛ⟨ 2 & 2 & !ₛ $ homotopy-naturality
            (λ p → ! (! (merid (pt X))) ∙ ap Susp-flip p ∙' ! (merid (pt X)))
            (λ p → Ω-fmap (⊙Susp-flip X) p)
            (λ p → ! (Ω-fmap-β (⊙Susp-flip X) p))
            (!-inv-r (merid (pt X))) ⟩
    custom-path-alg (merid (pt X)) (merid (pt X)) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (! (Susp-flip-σloop X (pt X))) ◃∙
    ap (λ p → ! (! (merid (pt X))) ∙ ap Susp-flip p ∙' ! (merid (pt X)))
       (!-inv-r (merid (pt X))) ◃∙
    ! (Ω-fmap-β (⊙Susp-flip X) idp) ◃∙
    snd (⊙Ω-fmap (⊙Susp-flip X)) ◃∎
      =ₛ⟨ 3 & 2 & pre-rotate'-in $ Ω-fmap-pt (⊙Susp-flip X) ⟩
    custom-path-alg (merid (pt X)) (merid (pt X)) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (! (Susp-flip-σloop X (pt X))) ◃∙
    ap (λ p → ! (! (merid (pt X))) ∙ ap Susp-flip p ∙' ! (merid (pt X)))
       (!-inv-r (merid (pt X))) ◃∙
    ap (! (! (merid (pt X))) ∙_) (∙'-unit-l (snd (⊙Susp-flip X))) ◃∙
    !-inv-l (snd (⊙Susp-flip X)) ◃∎
      =ₛ₁⟨ 2 & 1 & ap-∘ (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
                        (ap Susp-flip)
                        (!-inv-r (merid (pt X))) ⟩
    custom-path-alg (merid (pt X)) (merid (pt X)) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (! (Susp-flip-σloop X (pt X))) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (ap (ap Susp-flip) (!-inv-r (merid (pt X)))) ◃∙
    ap (! (! (merid (pt X))) ∙_) (∙'-unit-l (snd (⊙Susp-flip X))) ◃∙
    !-inv-l (snd (⊙Susp-flip X)) ◃∎
      =ₛ⟨ 1 & 2 & ap-seq-=ₛ (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X))) $
                  !ₛ $ post-rotate-out $ pre-rotate-in $ Susp-flip-σloop-pt X ⟩
    custom-path-alg (merid (pt X)) (merid (pt X)) ◃∙
    ap (λ q → ! (! (merid (pt X))) ∙ q ∙' ! (merid (pt X)))
       (!-inv-l (merid (pt X))) ◃∙
    ap (! (! (merid (pt X))) ∙_) (∙'-unit-l (! (merid (pt X)))) ◃∙
    !-inv-l (! (merid (pt X))) ◃∎
      =ₛ⟨ custom-path-alg-coh (merid (pt X)) ⟩
    ap ! (!-inv-r (merid (pt X))) ◃∎
      =ₛ⟨ 1 & 0 & contract ⟩
    ap ! (!-inv-r (merid (pt X))) ◃∙
    idp ◃∎ ∎ₛ
    where
    custom-path-alg-coh : ∀ {l} {A : Type l}
      {n s : A} (p : n == s)
      → custom-path-alg p p ◃∙
        ap (λ q → ! (! p) ∙ q ∙' ! p) (!-inv-l p) ◃∙
        ap (! (! p) ∙_) (∙'-unit-l (! p)) ◃∙
        !-inv-l (! p) ◃∎
        =ₛ
        ap ! (!-inv-r p) ◃∎
    custom-path-alg-coh p@idp = =ₛ-in idp

⊙Ω-!-⊙Susp-flip : ∀ {i} (X : Ptd i) (n : ℕ₋₂)
  → is-equiv (Trunc-fmap {n = n} (σloop X))
  → ⊙Trunc-fmap {n = n} ⊙Ω-! == ⊙Trunc-fmap {n = n} (⊙Ω-fmap (⊙Susp-flip X))
⊙Ω-!-⊙Susp-flip X n is-eq =
  –>-is-inj
    (pre⊙∘-equiv
      {Z = ⊙Trunc n (⊙Ω (⊙Susp (de⊙ X)))}
      (⊙Trunc-fmap {n = n} (⊙σloop X) , is-eq))
    (⊙Trunc-fmap {n = n} ⊙Ω-!)
    (⊙Trunc-fmap {n = n} (⊙Ω-fmap (⊙Susp-flip X)))
    (=⊙∘-out (⊙Trunc-fmap-seq-=⊙∘ {n = n} (⊙Ω-!-Susp-flip' X)))
