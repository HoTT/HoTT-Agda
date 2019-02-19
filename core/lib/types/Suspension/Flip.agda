{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Bool
open import lib.types.FunctionSeq
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Suspension.Core
open import lib.types.Suspension.Trunc
open import lib.types.Truncation

module lib.types.Suspension.Flip where

module SuspFlip {i} {A : Type i} = SuspRec
  (south' A) north (! ∘ merid)

Susp-flip : ∀ {i} {A : Type i} → Susp A → Susp A
Susp-flip = SuspFlip.f

Susp-flip-σloop-seq : ∀ {i} (X : Ptd i) (x : de⊙ X)
  → ap Susp-flip (σloop X x) =-= ! (merid x) ∙ merid (pt X)
Susp-flip-σloop-seq X x =
  ap Susp-flip (merid x ∙ ! (merid (pt X)))
    =⟪ ap-∙ Susp-flip (merid x) (! (merid (pt X))) ⟫
  ap Susp-flip (merid x) ∙ ap Susp-flip (! (merid (pt X)))
    =⟪ ap2 _∙_
           (! (!-! (ap Susp-flip (merid x))) ∙ ap ! (r x))
           (ap-! Susp-flip (merid (pt X)) ∙ r (pt X)) ⟫
  ! (merid x) ∙ merid (pt X) ∎∎
  where
    r : (x : de⊙ X) → ! (ap Susp-flip (merid x)) == merid x
    r x = ap ! (SuspFlip.merid-β x) ∙ !-! (merid x)

Susp-flip-σloop : ∀ {i} (X : Ptd i) (x : de⊙ X)
  → ap Susp-flip (σloop X x) == ! (merid x) ∙ merid (pt X)
Susp-flip-σloop X x = ↯ (Susp-flip-σloop-seq X x)

Susp-flip-σloop-pt : ∀ {i} (X : Ptd i)
  → Susp-flip-σloop X (pt X) ◃∎
    =ₛ
    ap (ap Susp-flip) (!-inv-r (merid (pt X))) ◃∙
    ! (!-inv-l (merid (pt X))) ◃∎
Susp-flip-σloop-pt X =
  Susp-flip-σloop X (pt X) ◃∎
    =ₛ⟨ expand (Susp-flip-σloop-seq X (pt X)) ⟩
  Susp-flip-σloop-seq X (pt X)
    =ₛ⟨ coh Susp-flip (merid (pt X)) (merid (pt X))
            (ap ! (SuspFlip.merid-β (pt X)) ∙ !-! (merid (pt X))) ⟩
  ap (ap Susp-flip) (!-inv-r (merid (pt X))) ◃∙
  ! (!-inv-l (merid (pt X))) ◃∎ ∎ₛ
  where
  coh : ∀ {j k} {A : Type j} {B : Type k} (f : A → B)
    {a₀ a₁ : A} (p : a₀ == a₁)
    (q : f a₁ == f a₀)
    (r : ! (ap f p) == q)
    → ap-∙ f p (! p) ◃∙
      ap2 _∙_ (! (!-! (ap f p)) ∙ ap ! r) (ap-! f p ∙ r) ◃∎
      =ₛ
      ap (ap f) (!-inv-r p) ◃∙
      ! (!-inv-l q) ◃∎
  coh f p@idp q@.idp r@idp = =ₛ-in idp

maybe-Susp-flip : ∀ {i} {A : Type i} → Bool → Susp A → Susp A
maybe-Susp-flip true = Susp-flip
maybe-Susp-flip false = idf _

⊙Susp-flip : ∀ {i} (X : Ptd i) → ⊙Susp (de⊙ X) ⊙→ ⊙Susp (de⊙ X)
⊙Susp-flip X = (Susp-flip , ! (merid (pt X)))

⊙maybe-Susp-flip : ∀ {i} (X : Ptd i) → Bool → ⊙Susp (de⊙ X) ⊙→ ⊙Susp (de⊙ X)
⊙maybe-Susp-flip X true  = ⊙Susp-flip X
⊙maybe-Susp-flip X false = ⊙idf (⊙Susp (de⊙ X))

de⊙-⊙maybe-Susp-flip : ∀ {i} (X : Ptd i) (b : Bool)
  → fst (⊙maybe-Susp-flip X b) == maybe-Susp-flip b
de⊙-⊙maybe-Susp-flip X true  = idp
de⊙-⊙maybe-Susp-flip X false = idp

Susp-flip-flip : ∀ {i} {A : Type i} (sa : Susp A)
  → Susp-flip (Susp-flip sa) == sa
Susp-flip-flip =
  Susp-elim
    idp
    idp $ λ a → ↓-='-in' $
  ap (λ z → z) (merid a)
    =⟨ ap-idf (merid a) ⟩
  merid a
    =⟨ ! (!-! (merid a)) ⟩
  ! (! (merid a))
    =⟨ ap ! (! (SuspFlip.merid-β a)) ⟩
  ! (ap Susp-flip (merid a))
    =⟨ !-ap Susp-flip (merid a) ⟩
  ap Susp-flip (! (merid a))
    =⟨ ap (ap Susp-flip) (! (SuspFlip.merid-β a)) ⟩
  ap Susp-flip (ap Susp-flip (merid a))
    =⟨ ∘-ap Susp-flip Susp-flip (merid a) ⟩
  ap (Susp-flip ∘ Susp-flip) (merid a) =∎

⊙Susp-flip-flip : ∀ {i} {X : Ptd i}
  → ⊙Susp-flip X ◃⊙∘ ⊙Susp-flip X ◃⊙idf =⊙∘ ⊙idf-seq
⊙Susp-flip-flip {_} {X} =
  ⊙seq-λ= Susp-flip-flip $
  ap Susp-flip (! (merid (pt X))) ◃∙
  ! (merid (pt X)) ◃∎
    =ₛ₁⟨ 0 & 1 & ap-! Susp-flip (merid (pt X)) ⟩
  ! (ap Susp-flip (merid (pt X))) ◃∙
  ! (merid (pt X)) ◃∎
    =ₛ₁⟨ 0 & 1 & ap ! (SuspFlip.merid-β (pt X)) ⟩
  ! (! (merid (pt X))) ◃∙
  ! (merid (pt X)) ◃∎
    =ₛ₁⟨ !-inv-l (! (merid (pt X))) ⟩
  idp ◃∎ ∎ₛ

⊙maybe-Susp-flip-flip : ∀ {i} (X : Ptd i) (b c : Bool)
  → ⊙maybe-Susp-flip X b ◃⊙∘ ⊙maybe-Susp-flip X c ◃⊙idf
    =⊙∘
    ⊙maybe-Susp-flip X (xor b c) ◃⊙idf
⊙maybe-Susp-flip-flip X true  true  =
  ⊙Susp-flip X ◃⊙∘ ⊙Susp-flip X ◃⊙idf
    =⊙∘⟨ ⊙Susp-flip-flip ⟩
  ⊙idf-seq
    =⊙∘⟨ ⊙contract ⟩
  ⊙idf _ ◃⊙idf ∎⊙∘
⊙maybe-Susp-flip-flip X true  false = =⊙∘-in idp
⊙maybe-Susp-flip-flip X false true  = =⊙∘-in (⊙λ= (⊙∘-unit-l (⊙Susp-flip X)))
⊙maybe-Susp-flip-flip X false false = =⊙∘-in idp

Susp-flip-equiv : ∀ {i} {A : Type i} → Susp A ≃ Susp A
Susp-flip-equiv {A = A} =
  equiv Susp-flip Susp-flip Susp-flip-flip Susp-flip-flip

Susp-flip-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B)
  → ∀ σ → Susp-flip (Susp-fmap f σ) == Susp-fmap f (Susp-flip σ)
Susp-flip-natural f = Susp-elim idp idp $ λ y → ↓-='-in' $
  ap (Susp-fmap f ∘ Susp-flip) (merid y)
    =⟨ ap-∘ (Susp-fmap f) Susp-flip (merid y) ⟩
  ap (Susp-fmap f) (ap Susp-flip (merid y))
    =⟨ ap (ap (Susp-fmap f)) (SuspFlip.merid-β y) ⟩
  ap (Susp-fmap f) (! (merid y))
    =⟨ ap-! (Susp-fmap f) (merid y) ⟩
  ! (ap (Susp-fmap f) (merid y))
    =⟨ ap ! (SuspFmap.merid-β f y) ⟩
  ! (merid (f y))
    =⟨ ! (SuspFlip.merid-β (f y)) ⟩
  ap Susp-flip (merid (f y))
    =⟨ ! (ap (ap Susp-flip) (SuspFmap.merid-β f y)) ⟩
  ap Susp-flip (ap (Susp-fmap f) (merid y))
    =⟨ ∘-ap Susp-flip (Susp-fmap f) (merid y) ⟩
  ap (Susp-flip ∘ Susp-fmap f) (merid y) =∎

⊙Susp-flip-natural : ∀ {i} {j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
  → ⊙Susp-flip Y ⊙∘ ⊙Susp-fmap (fst f) == ⊙Susp-fmap (fst f) ⊙∘ ⊙Susp-flip X
⊙Susp-flip-natural {_} {_} {X} {Y} f =
  pair= (λ= (Susp-flip-natural (fst f))) $
  ↓-app=cst-in $ ! $ =ₛ-out {t = ! (merid (pt Y)) ◃∎} $
  app= (λ= (Susp-flip-natural (fst f))) north ◃∙
  ap (Susp-fmap (fst f)) (! (merid (pt X))) ◃∙
  idp ◃∎
    =ₛ⟨ 2 & 1 & expand [] ⟩
  app= (λ= (Susp-flip-natural (fst f))) north ◃∙
  ap (Susp-fmap (fst f)) (! (merid (pt X))) ◃∎
    =ₛ₁⟨ 0 & 1 & app=-β (Susp-flip-natural (fst f)) north ⟩
  idp ◃∙
  ap (Susp-fmap (fst f)) (! (merid (pt X))) ◃∎
    =ₛ⟨ 0 & 1 & expand [] ⟩
  ap (Susp-fmap (fst f)) (! (merid (pt X))) ◃∎
    =ₛ₁⟨ ap-! (Susp-fmap (fst f)) (merid (pt X)) ⟩
  ! (ap (Susp-fmap (fst f)) (merid (pt X))) ◃∎
    =ₛ₁⟨ ap ! (SuspFmap.merid-β (fst f) (pt X)) ⟩
  ! (merid (fst f (pt X))) ◃∎
    =ₛ₁⟨ ap (! ∘ merid) (snd f) ⟩
  ! (merid (pt Y)) ◃∎ ∎ₛ

module _ {i} {A : Type i} where

  Susp-fmap-flip : (x : Susp (Susp A))
    → Susp-fmap Susp-flip x == Susp-flip x
  Susp-fmap-flip =
    Susp-elim
      {P = λ x → Susp-fmap Susp-flip x == Susp-flip x}
      (merid north)
      (! (merid south)) $ λ y →
    ↓-='-in-=ₛ $
    merid north ◃∙
    ap Susp-flip (merid y) ◃∎
      =ₛ₁⟨ 1 & 1 & SuspFlip.merid-β y ⟩
    merid north ◃∙
    ! (merid y) ◃∎
      =ₛ⟨ =ₛ-in {t = merid (Susp-flip y) ◃∙ ! (merid south) ◃∎} $
          Susp-elim
             {P = λ y → merid north ∙ ! (merid y) == merid (Susp-flip y) ∙ ! (merid south)}
             (!-inv-r (merid north) ∙ ! (!-inv-r (merid south)))
             idp
             (λ a → ↓-='-in-=ₛ $
               (!-inv-r (merid north) ∙ ! (!-inv-r (merid south))) ◃∙
               ap (λ z → merid (Susp-flip z) ∙ ! (merid south)) (merid a) ◃∎
                 =ₛ⟨ 0 & 1 & expand (!-inv-r (merid north) ◃∙ ! (!-inv-r (merid south)) ◃∎) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z → merid (Susp-flip z) ∙ ! (merid south)) (merid a) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap-∘ (λ z' → merid z' ∙ ! (merid south)) Susp-flip (merid a) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z' → merid z' ∙ ! (merid south)) (ap Susp-flip (merid a)) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap (ap (λ z' → merid z' ∙ ! (merid south)))
                                 (SuspFlip.merid-β a) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z' → merid z' ∙ ! (merid south)) (! (merid a)) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap-∘ (_∙ ! (merid south)) merid (! (merid a)) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (_∙ ! (merid south)) (ap merid (! (merid a))) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap (ap (_∙ ! (merid south))) (ap-! merid (merid a)) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (_∙ ! (merid south)) (! (ap merid (merid a))) ◃∎
                 =ₛ⟨ coh-helper (ap merid (merid a)) ⟩
               ap (λ q → merid north ∙ ! q) (ap merid (merid a)) ◃∎
                 =ₛ₁⟨ ∘-ap (λ q → merid north ∙ ! q) merid (merid a) ⟩
               ap (λ z → merid north ∙ ! (merid z)) (merid a) ◃∎
                 =ₛ⟨ 1 & 0 & contract ⟩
               ap (λ z → merid north ∙ ! (merid z)) (merid a) ◃∙ idp ◃∎ ∎ₛ)
             y ⟩
    merid (Susp-flip y) ◃∙
    ! (merid south) ◃∎
      =ₛ₁⟨ 0 & 1 & ! (SuspFmap.merid-β Susp-flip y) ⟩
    ap (Susp-fmap Susp-flip) (merid y) ◃∙
    ! (merid south) ◃∎ ∎ₛ
    where
      coh-helper : ∀ {j} {B : Type j}
        {b-north b-south : B}
        {merid₁ merid₂ : b-north == b-south}
        (p : merid₁ == merid₂)
        → !-inv-r merid₁ ◃∙
          ! (!-inv-r merid₂) ◃∙
          ap (_∙ ! merid₂) (! p) ◃∎
          =ₛ
          ap (λ q → merid₁ ∙ ! q) p ◃∎
      coh-helper {merid₁ = idp} {merid₂ = .idp} idp =
        =ₛ-in idp

  ⊙Susp-fmap-Susp-flip : ⊙Susp-fmap Susp-flip == ⊙Susp-flip (⊙Susp A)
  ⊙Susp-fmap-Susp-flip =
    ⊙λ=' Susp-fmap-flip (↓-idf=cst-in (! (!-inv-r (merid north))))

  ⊙Susp-fmap-maybe-Susp-flip : ∀ (b : Bool)
    → ⊙Susp-fmap (maybe-Susp-flip b) == ⊙maybe-Susp-flip (⊙Susp A) b
  ⊙Susp-fmap-maybe-Susp-flip true  = ⊙Susp-fmap-Susp-flip
  ⊙Susp-fmap-maybe-Susp-flip false = =⊙∘-out (⊙Susp-fmap-idf _)

⊙maybe-Susp-flip-natural : ∀ {i} {j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) (b : Bool)
  → ⊙Susp-fmap (fst f) ⊙∘ ⊙maybe-Susp-flip X b ==
    ⊙maybe-Susp-flip Y b ⊙∘ ⊙Susp-fmap (fst f)
⊙maybe-Susp-flip-natural f true  = ! (⊙Susp-flip-natural f)
⊙maybe-Susp-flip-natural f false = ⊙λ= (⊙∘-unit-l (⊙Susp-fmap (fst f)))

module _ {i} (A : Type i) (m : ℕ₋₂) where

  Susp-Trunc-swap-Susp-flip :
    Susp-Trunc-swap A m ∘ Susp-flip ∼
    Trunc-fmap Susp-flip ∘ Susp-Trunc-swap A m
  Susp-Trunc-swap-Susp-flip =
    Susp-elim
      idp
      idp $
    Trunc-elim {{λ t → ↓-level (=-preserves-level Trunc-level)}} $ λ a →
    ↓-='-in' $
    ap (Trunc-fmap Susp-flip ∘ Susp-Trunc-swap A m) (merid [ a ])
      =⟨ ap-∘ (Trunc-fmap Susp-flip) (Susp-Trunc-swap A m) (merid [ a ]) ⟩
    ap (Trunc-fmap Susp-flip) (ap (Susp-Trunc-swap A m) (merid [ a ]))
      =⟨ ap (ap (Trunc-fmap Susp-flip)) (SuspTruncSwap.merid-β A m [ a ]) ⟩
    ap (Trunc-fmap Susp-flip) (ap [_] (merid a))
      =⟨ ∘-ap (Trunc-fmap Susp-flip) [_] (merid a) ⟩
    ap ([_] ∘ Susp-flip) (merid a)
      =⟨ ap-∘ [_] Susp-flip (merid a) ⟩
    ap [_] (ap Susp-flip (merid a))
      =⟨ ap (ap [_]) (SuspFlip.merid-β a) ⟩
    ap [_] (! (merid a))
      =⟨ ap-! [_] (merid a) ⟩
    ! (ap [_] (merid a))
      =⟨ ap ! (! (SuspTruncSwap.merid-β A m [ a ])) ⟩
    ! (ap (Susp-Trunc-swap A m) (merid [ a ]))
      =⟨ !-ap (Susp-Trunc-swap A m) (merid [ a ]) ⟩
    ap (Susp-Trunc-swap A m) (! (merid [ a ]))
      =⟨ ap (ap (Susp-Trunc-swap A m)) (! (SuspFlip.merid-β [ a ])) ⟩
    ap (Susp-Trunc-swap A m) (ap Susp-flip (merid [ a ]))
      =⟨ ∘-ap (Susp-Trunc-swap A m) Susp-flip (merid [ a ]) ⟩
    ap (Susp-Trunc-swap A m ∘ Susp-flip) (merid [ a ]) =∎

abstract
  ⊙Susp-Trunc-swap-⊙Susp-flip : ∀ {i} {X : Ptd i} (m : ℕ₋₂)
    → ⊙Susp-Trunc-swap (de⊙ X) m ◃⊙∘
      ⊙Susp-flip (⊙Trunc m X) ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙Susp-flip X) ◃⊙∘
      ⊙Susp-Trunc-swap (de⊙ X) m ◃⊙idf
  ⊙Susp-Trunc-swap-⊙Susp-flip {X = X} m =
    ⊙seq-λ= (Susp-Trunc-swap-Susp-flip (de⊙ X) m) $ !ₛ $
    idp ◃∙
    idp ◃∙
    ap [_] (! (merid (pt X))) ◃∎
      =ₛ⟨ 0 & 1 & expand [] ⟩
    idp ◃∙
    ap [_] (! (merid (pt X))) ◃∎
      =ₛ⟨ 0 & 1 & expand [] ⟩
    ap [_] (! (merid (pt X))) ◃∎
      =ₛ₁⟨ ap-! [_] (merid (pt X)) ⟩
    ! (ap [_] (merid (pt X))) ◃∎
      =ₛ₁⟨ ! $ ap ! $ SuspTruncSwap.merid-β (de⊙ X) m [ pt X ] ⟩
    ! (ap (Susp-Trunc-swap (de⊙ X) m) (merid [ pt X ])) ◃∎
      =ₛ₁⟨ !-ap (Susp-Trunc-swap (de⊙ X) m) (merid [ pt X ]) ⟩
    ap (Susp-Trunc-swap (de⊙ X) m) (! (merid [ pt X ])) ◃∎
      =ₛ⟨ 1 & 0 & contract ⟩
    ap (Susp-Trunc-swap (de⊙ X) m) (! (merid [ pt X ])) ◃∙
    idp ◃∎ ∎ₛ
