{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.FunctionSeq
open import lib.types.Nat
open import lib.types.Pointed
open import lib.types.Suspension.Core
open import lib.types.Suspension.Iterated

module lib.types.Suspension.IteratedEquivs where

Susp^-+ : ∀ {i} (m n : ℕ) {A : Type i}
  → Susp^ m (Susp^ n A) == Susp^ (m + n) A
Susp^-+ O n = idp
Susp^-+ (S m) n = ap Susp (Susp^-+ m n)

⊙Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) == ⊙Susp^ (m + n) X
⊙Susp^-+ 0 n {X} = idp
⊙Susp^-+ (S m) n {X} = ap ⊙Susp (Susp^-+ m n)

de⊙-⊙Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ap de⊙ (⊙Susp^-+ m n {X}) == Susp^-+ m n {de⊙ X}
de⊙-⊙Susp^-+ 0 n {X} = idp
de⊙-⊙Susp^-+ (S m) n {X} = ∘-ap de⊙ ⊙Susp (Susp^-+ m n)

Susp^-+-0-r : ∀ {i} (m : ℕ) {A : Type i}
  → Susp^-+ m 0 ◃∙ ap (λ k → Susp^ k A) (+-unit-r m) ◃∎ =ₛ []
Susp^-+-0-r O {A} = =ₛ-in $
  ap (ap (λ k → Susp^ k A))
     (set-path ℕ-level (+-unit-r 0) idp)
Susp^-+-0-r (S m) {A} =
  ap Susp (Susp^-+ m 0) ◃∙
  ap (λ k → Susp^ k A) (+-unit-r (S m)) ◃∎
    =ₛ₁⟨ 1 & 1 & ap (ap (λ k → Susp^ k A)) $
                 set-path ℕ-level (+-unit-r (S m)) (ap S (+-unit-r m)) ⟩
  ap Susp (Susp^-+ m 0) ◃∙
  ap (λ k → Susp^ k A) (ap S (+-unit-r m)) ◃∎
    =ₛ₁⟨ 1 & 1 &
         ∘-ap (λ k → Susp^ k A) S (+-unit-r m) ∙
         ap-∘ Susp (λ k → Susp^ k A) (+-unit-r m) ⟩
  ap Susp (Susp^-+ m 0) ◃∙
  ap Susp (ap (λ k → Susp^ k A) (+-unit-r m)) ◃∎
    =ₛ⟨ ap-seq-=ₛ Susp (Susp^-+-0-r m) ⟩
  [] ∎ₛ

⊙Susp^-+-0-r : ∀ {i} (m : ℕ) {X : Ptd i}
  → ⊙Susp^-+ m 0 ◃∙ ap (λ k → ⊙Susp^ k X) (+-unit-r m) ◃∎ =ₛ []
⊙Susp^-+-0-r 0 {X} = =ₛ-in $
  ap (ap (λ k → ⊙Susp^ k X))
     (set-path ℕ-level (+-unit-r 0) idp)
⊙Susp^-+-0-r (S m) {X} =
  ap ⊙Susp (Susp^-+ m 0) ◃∙
  ap (λ k → ⊙Susp^ k X) (+-unit-r (S m)) ◃∎
    =ₛ₁⟨ 1 & 1 & ap (ap (λ k → ⊙Susp^ k X)) $
                 set-path ℕ-level (+-unit-r (S m)) (ap S (+-unit-r m)) ⟩
  ap ⊙Susp (Susp^-+ m 0) ◃∙
  ap (λ k → ⊙Susp^ k X) (ap S (+-unit-r m)) ◃∎
    =ₛ₁⟨ 1 & 1 &
         ∘-ap (λ k → ⊙Susp^ k X) S (+-unit-r m) ∙
         ap-∘ ⊙Susp (λ k → Susp^ k (de⊙ X)) (+-unit-r m) ⟩
  ap ⊙Susp (Susp^-+ m 0) ◃∙
  ap ⊙Susp (ap (λ k → Susp^ k (de⊙ X)) (+-unit-r m)) ◃∎
    =ₛ⟨ ap-seq-=ₛ ⊙Susp (Susp^-+-0-r m) ⟩
  [] ∎ₛ

Susp^-+-assoc-coh : ∀ {i} (m n o : ℕ) {A : Type i}
  → ap (Susp^ m) (Susp^-+ n o {A}) ◃∙
    Susp^-+ m (n + o) {A} ◃∎
    =ₛ
    Susp^-+ m n {Susp^ o A} ◃∙
    Susp^-+ (m + n) o ◃∙
    ap (λ k → Susp^ k A) (+-assoc m n o) ◃∎
Susp^-+-assoc-coh O n o {A} =
  ap (idf _) (Susp^-+ n o {A}) ◃∙
  idp ◃∎
    =ₛ₁⟨ 0 & 1 & ap-idf (Susp^-+ n o {A}) ⟩
  Susp^-+ n o {A} ◃∙
  idp ◃∎
    =ₛ₁⟨ 1 & 1 & ap (ap (λ k → Susp^ k A)) $
         set-path ℕ-level idp (+-assoc 0 n o) ⟩
  Susp^-+ n o {A} ◃∙
  ap (λ k → Susp^ k A) (+-assoc 0 n o) ◃∎
    =ₛ⟨ 0 & 0 & contract ⟩
  idp ◃∙
  Susp^-+ n o {A} ◃∙
  ap (λ k → Susp^ k A) (+-assoc 0 n o) ◃∎ ∎ₛ
Susp^-+-assoc-coh (S m) n o {A} =
  ap (Susp ∘ Susp^ m) (Susp^-+ n o {A}) ◃∙
  ap Susp (Susp^-+ m (n + o) {A}) ◃∎
    =ₛ₁⟨ 0 & 1 & ap-∘ Susp (Susp^ m) (Susp^-+ n o {A}) ⟩
  ap Susp (ap (Susp^ m) (Susp^-+ n o {A})) ◃∙
  ap Susp (Susp^-+ m (n + o) {A}) ◃∎
    =ₛ⟨ ap-seq-=ₛ Susp (Susp^-+-assoc-coh m n o) ⟩
  ap Susp (Susp^-+ m n) ◃∙
  ap Susp (Susp^-+ (m + n) o) ◃∙
  ap Susp (ap (λ k → Susp^ k A) (+-assoc m n o)) ◃∎
    =ₛ₁⟨ 2 & 1 & ∘-ap Susp (λ k → Susp^ k A) (+-assoc m n o) ∙
                 ap-∘ (λ k → Susp^ k A) S (+-assoc m n o) ⟩
  ap Susp (Susp^-+ m n) ◃∙
  ap Susp (Susp^-+ (m + n) o) ◃∙
  ap (λ k → Susp^ k A) (ap S (+-assoc m n o)) ◃∎
    =ₛ₁⟨ 2 & 1 & ap (ap (λ k → Susp^ k A)) $
                 set-path ℕ-level (ap S (+-assoc m n o)) (+-assoc (S m) n o) ⟩
  ap Susp (Susp^-+ m n) ◃∙
  ap Susp (Susp^-+ (m + n) o) ◃∙
  ap (λ k → Susp^ k A) (+-assoc (S m) n o) ◃∎ ∎ₛ

⊙Susp^-+-assoc-coh : ∀ {i} (m n o : ℕ) {X : Ptd i}
  → ap (⊙Susp^ m) (⊙Susp^-+ n o {X}) ◃∙
    ⊙Susp^-+ m (n + o) {X} ◃∎
    =ₛ
    ⊙Susp^-+ m n {⊙Susp^ o X} ◃∙
    ⊙Susp^-+ (m + n) o ◃∙
    ap (λ k → ⊙Susp^ k X) (+-assoc m n o) ◃∎
⊙Susp^-+-assoc-coh O n o {X} =
  ap (idf _) (⊙Susp^-+ n o) ◃∙
  idp ◃∎
    =ₛ₁⟨ 0 & 1 & ap-idf (⊙Susp^-+ n o) ⟩
  ⊙Susp^-+ n o ◃∙
  idp ◃∎
    =ₛ₁⟨ 1 & 1 & ap (ap (λ k → ⊙Susp^ k X)) $
                 set-path ℕ-level idp (+-assoc 0 n o) ⟩
  ⊙Susp^-+ n o ◃∙
  ap (λ k → ⊙Susp^ k X) (+-assoc 0 n o) ◃∎
    =ₛ⟨ 0 & 0 & contract ⟩
  idp ◃∙
  ⊙Susp^-+ n o ◃∙
  ap (λ k → ⊙Susp^ k X) (+-assoc 0 n o) ◃∎ ∎ₛ
⊙Susp^-+-assoc-coh (S m) n o {X} =
  ap (⊙Susp ∘ Susp^ m ∘ de⊙) (⊙Susp^-+ n o {X}) ◃∙
  ap ⊙Susp (Susp^-+ m (n + o) {de⊙ X}) ◃∎
    =ₛ₁⟨ 0 & 1 & ap-∘ (⊙Susp ∘ Susp^ m) de⊙ (⊙Susp^-+ n o {X}) ⟩
  ap (⊙Susp ∘ Susp^ m) (ap de⊙ (⊙Susp^-+ n o {X})) ◃∙
  ap ⊙Susp (Susp^-+ m (n + o) {de⊙ X}) ◃∎
    =ₛ₁⟨ 0 & 1 & ap (ap (⊙Susp ∘ Susp^ m)) (de⊙-⊙Susp^-+ n o {X}) ⟩
  ap (⊙Susp ∘ Susp^ m) (Susp^-+ n o {de⊙ X}) ◃∙
  ap ⊙Susp (Susp^-+ m (n + o) {de⊙ X}) ◃∎
    =ₛ₁⟨ 0 & 1 & ap-∘ ⊙Susp (Susp^ m) (Susp^-+ n o {de⊙ X}) ⟩
  ap ⊙Susp (ap (Susp^ m) (Susp^-+ n o {de⊙ X})) ◃∙
  ap ⊙Susp (Susp^-+ m (n + o) {de⊙ X}) ◃∎
    =ₛ⟨ ap-seq-=ₛ ⊙Susp (Susp^-+-assoc-coh m n o) ⟩
  ap ⊙Susp (Susp^-+ m n) ◃∙
  ap ⊙Susp (Susp^-+ (m + n) o) ◃∙
  ap ⊙Susp (ap (λ k → Susp^ k (de⊙ X)) (+-assoc m n o)) ◃∎
    =ₛ₁⟨ 2 & 1 & ∘-ap ⊙Susp (λ k → Susp^ k (de⊙ X)) (+-assoc m n o) ∙
                 ap-∘ (λ k → ⊙Susp^ k X) S (+-assoc m n o) ⟩
  ap ⊙Susp (Susp^-+ m n) ◃∙
  ap ⊙Susp (Susp^-+ (m + n) o) ◃∙
  ap (λ k → ⊙Susp^ k X) (ap S (+-assoc m n o)) ◃∎
    =ₛ₁⟨ 2 & 1 & ap (ap (λ k → ⊙Susp^ k X)) $
                 set-path ℕ-level (ap S (+-assoc m n o)) (+-assoc (S m) n o) ⟩
  ap ⊙Susp (Susp^-+ m n) ◃∙
  ap ⊙Susp (Susp^-+ (m + n) o) ◃∙
  ap (λ k → ⊙Susp^ k X) (+-assoc (S m) n o) ◃∎ ∎ₛ

Susp^-comm-seq : ∀ {i} (m n : ℕ) {A : Type i}
  → Susp^ m (Susp^ n A) =-= Susp^ n (Susp^ m A)
Susp^-comm-seq m n {A} =
  Susp^ m (Susp^ n A)
    =⟪ Susp^-+ m n ⟫
  Susp^ (m + n) A
    =⟪ ap (λ k → Susp^ k A) (+-comm m n) ⟫
  Susp^ (n + m) A
    =⟪ ! (Susp^-+ n m) ⟫
  Susp^ n (Susp^ m A) ∎∎

Susp^-comm : ∀ {i} (m n : ℕ) {A : Type i}
  → Susp^ m (Susp^ n A) == Susp^ n (Susp^ m A)
Susp^-comm m n {A} = ↯ (Susp^-comm-seq m n {A})

⊙Susp^-comm-seq : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) =-= ⊙Susp^ n (⊙Susp^ m X)
⊙Susp^-comm-seq m n {X} =
  ⊙Susp^ m (⊙Susp^ n X)
    =⟪ ⊙Susp^-+ m n ⟫
  ⊙Susp^ (m + n) X
    =⟪ ap (λ k → ⊙Susp^ k X) (+-comm m n) ⟫
  ⊙Susp^ (n + m) X
    =⟪ ! (⊙Susp^-+ n m) ⟫
  ⊙Susp^ n (⊙Susp^ m X) ∎∎

⊙Susp^-comm : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) == ⊙Susp^ n (⊙Susp^ m X)
⊙Susp^-comm m n {X} = ↯ (⊙Susp^-comm-seq m n {X})

de⊙-⊙Susp^-comm : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ap de⊙ (⊙Susp^-comm m n {X}) == Susp^-comm m n {de⊙ X}
de⊙-⊙Susp^-comm m n {X} = =ₛ-out {t = Susp^-comm m n {de⊙ X} ◃∎} $
  ap de⊙ (⊙Susp^-comm m n {X}) ◃∎
    =ₛ⟨ ap-seq-∙ de⊙ (⊙Susp^-comm-seq m n {X}) ⟩
  ap de⊙ (⊙Susp^-+ m n) ◃∙
  ap de⊙ (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃∙
  ap de⊙ (! (⊙Susp^-+ n m)) ◃∎
    =ₛ₁⟨ 0 & 1 & de⊙-⊙Susp^-+ m n ⟩
  Susp^-+ m n ◃∙
  ap de⊙ (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃∙
  ap de⊙ (! (⊙Susp^-+ n m)) ◃∎
    =ₛ₁⟨ 1 & 1 & ∘-ap de⊙ (λ k → ⊙Susp^ k X) (+-comm m n) ⟩
  Susp^-+ m n ◃∙
  ap (λ k → Susp^ k (de⊙ X)) (+-comm m n) ◃∙
  ap de⊙ (! (⊙Susp^-+ n m)) ◃∎
    =ₛ₁⟨ 2 & 1 & ap-! de⊙ (⊙Susp^-+ n m) ⟩
  Susp^-+ m n ◃∙
  ap (λ k → Susp^ k (de⊙ X)) (+-comm m n) ◃∙
  ! (ap de⊙ (⊙Susp^-+ n m)) ◃∎
    =ₛ₁⟨ 2 & 1 & ap ! (de⊙-⊙Susp^-+ n m) ⟩
  Susp^-+ m n ◃∙
  ap (λ k → Susp^ k (de⊙ X)) (+-comm m n) ◃∙
  ! (Susp^-+ n m) ◃∎
    =ₛ⟨ contract ⟩
  Susp^-comm m n ◃∎ ∎ₛ

⊙Susp^-swap : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) ⊙→ ⊙Susp^ n (⊙Susp^ m X)
⊙Susp^-swap m n {X} = ⊙coe (⊙Susp^-comm m n {X})

abstract
  ⊙Susp^-comm-diag : ∀ {i} (m : ℕ) {X : Ptd i}
    → ⊙Susp^-comm m m {X} ◃∎ =ₛ []
  ⊙Susp^-comm-diag m {X} =
    ↯ (⊙Susp^-comm-seq m m {X}) ◃∎
      =ₛ⟨ expand (⊙Susp^-comm-seq m m {X}) ⟩
    ⊙Susp^-+ m m ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m m) ◃∙
    ! (⊙Susp^-+ m m) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → ⊙Susp^ k X)) (set-path ℕ-level (+-comm m m) idp) ⟩
    ⊙Susp^-+ m m ◃∙
    idp ◃∙
    ! (⊙Susp^-+ m m) ◃∎
      =ₛ⟨ 1 & 1 & expand [] ⟩
    ⊙Susp^-+ m m ◃∙
    ! (⊙Susp^-+ m m) ◃∎
      =ₛ⟨ seq-!-inv-r (⊙Susp^-+ m m ◃∎) ⟩
    [] ∎ₛ

  Susp^-comm-! : ∀ {i} (m n : ℕ) {A : Type i}
    → ! (Susp^-comm m n {A}) == Susp^-comm n m
  Susp^-comm-! m n {A} = =ₛ-out $
    ! (↯ (Susp^-comm-seq m n {A})) ◃∎
      =ₛ⟨ !-∙-seq (Susp^-comm-seq m n {A}) ⟩
    ! (! (Susp^-+ n m)) ◃∙
    ! (ap (λ k → Susp^ k A) (+-comm m n)) ◃∙
    ! (Susp^-+ m n) ◃∎
      =ₛ₁⟨ 0 & 1 & !-! (Susp^-+ n m) ⟩
    Susp^-+ n m ◃∙
    ! (ap (λ k → Susp^ k A) (+-comm m n)) ◃∙
    ! (Susp^-+ m n) ◃∎
      =ₛ₁⟨ 1 & 1 & !-ap (λ k → Susp^ k A) (+-comm m n) ⟩
    Susp^-+ n m ◃∙
    ap (λ k → Susp^ k A) (! (+-comm m n)) ◃∙
    ! (Susp^-+ m n) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → Susp^ k A)) $
           set-path ℕ-level (! (+-comm m n)) (+-comm n m) ⟩
    Susp^-+ n m ◃∙
    ap (λ k → Susp^ k A) (+-comm n m) ◃∙
    ! (Susp^-+ m n) ◃∎ ∎ₛ

  ⊙Susp^-comm-! : ∀ {i} (m n : ℕ) {X : Ptd i}
    → ! (⊙Susp^-comm m n {X}) == ⊙Susp^-comm n m
  ⊙Susp^-comm-! m n {X} = =ₛ-out $
    ! (↯ (⊙Susp^-comm-seq m n {X})) ◃∎
      =ₛ⟨ !-∙-seq (⊙Susp^-comm-seq m n {X}) ⟩
    ! (! (⊙Susp^-+ n m)) ◃∙
    ! (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃∙
    ! (⊙Susp^-+ m n) ◃∎
      =ₛ₁⟨ 0 & 1 & !-! (⊙Susp^-+ n m) ⟩
    ⊙Susp^-+ n m ◃∙
    ! (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃∙
    ! (⊙Susp^-+ m n) ◃∎
      =ₛ₁⟨ 1 & 1 & !-ap (λ k → ⊙Susp^ k X) (+-comm m n) ⟩
    ⊙Susp^-+ n m ◃∙
    ap (λ k → ⊙Susp^ k X) (! (+-comm m n)) ◃∙
    ! (⊙Susp^-+ m n) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → ⊙Susp^ k X)) $
           set-path ℕ-level (! (+-comm m n)) (+-comm n m) ⟩
    ⊙Susp^-+ n m ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm n m) ◃∙
    ! (⊙Susp^-+ m n) ◃∎ ∎ₛ

  ⊙Susp^-comm-0-r : ∀ {i} (m : ℕ) (X : Ptd i)
    → ⊙Susp^-comm m 0 {X} == idp
  ⊙Susp^-comm-0-r m X = =ₛ-out $
    ⊙Susp^-+ m 0 ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m 0) ◃∙
    ! (⊙Susp^-+ 0 m) ◃∎
      =ₛ⟨ 2 & 1 & expand [] ⟩
    ⊙Susp^-+ m 0 ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m 0) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → ⊙Susp^ k X)) $
                  set-path ℕ-level (+-comm m 0) (+-unit-r m) ⟩
    ⊙Susp^-+ m 0 ◃∙
    ap (λ k → ⊙Susp^ k X) (+-unit-r m) ◃∎
      =ₛ⟨ ⊙Susp^-+-0-r m ⟩
    [] ∎ₛ

  ⊙Susp^-comm-0-l : ∀ {i} (n : ℕ) (X : Ptd i)
    → ⊙Susp^-comm 0 n {X} == idp
  ⊙Susp^-comm-0-l n X =
    ⊙Susp^-comm 0 n {X}
      =⟨ ! (⊙Susp^-comm-! n 0 {X}) ⟩
    ! (⊙Susp^-comm n 0 {X})
      =⟨ ap ! (⊙Susp^-comm-0-r n X) ⟩
    idp =∎

  ⊙Susp^-comm-S-r : ∀ {i} (m n : ℕ) {X : Ptd i}
    → ⊙Susp^-comm m (S n) {X} ◃∎ =ₛ ⊙Susp^-comm m 1 {⊙Susp^ n X} ◃∙ ap ⊙Susp (Susp^-comm m n) ◃∎
  ⊙Susp^-comm-S-r m n {X} =
    ⊙Susp^-comm m (S n) {X} ◃∎
      =ₛ⟨ expand (⊙Susp^-comm-seq m (S n) {X}) ⟩
    ⊙Susp^-+ m (S n) ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m (S n)) ◃∙
    ! (⊙Susp^-+ (S n) m {X}) ◃∎
      =ₛ⟨ 0 & 0 & contract ⟩
    idp ◃∙
    ⊙Susp^-+ m (S n) ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m (S n)) ◃∙
    ! (⊙Susp^-+ (S n) m {X}) ◃∎
      =ₛ⟨ 0 & 2 & ⊙Susp^-+-assoc-coh m 1 n ⟩
    ⊙Susp^-+ m 1 ◃∙
    ⊙Susp^-+ (m + 1) n ◃∙
    ap (λ k → ⊙Susp^ k X) (+-assoc m 1 n) ◃∙
    ap (λ k → ⊙Susp^ k X) (+-comm m (S n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 2 & 2 & ap-seq-=ₛ (λ k → ⊙Susp^ k X) $
          =ₛ-in {s = +-assoc m 1 n ◃∙ +-comm m (S n) ◃∎}
                {t = ap (_+ n) (+-comm m 1) ◃∙ ap S (+-comm m n) ◃∎} $
          set-path ℕ-level _ _ ⟩
    ⊙Susp^-+ m 1 ◃∙
    ⊙Susp^-+ (m + 1) n ◃∙
    ap (λ k → ⊙Susp^ k X) (ap (_+ n) (+-comm m 1)) ◃∙
    ap (λ k → ⊙Susp^ k X) (ap S (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 2 & 1 & ∘-ap (λ k → ⊙Susp^ k X) (_+ n) (+-comm m 1) ⟩
    ⊙Susp^-+ m 1 ◃∙
    ⊙Susp^-+ (m + 1) n ◃∙
    ap (λ k → ⊙Susp^ (k + n) X) (+-comm m 1) ◃∙
    ap (λ k → ⊙Susp^ k X) (ap S (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 1 & 2 & !ₛ $ homotopy-naturality
            (λ l → ⊙Susp^ l (⊙Susp^ n X))
            (λ l → ⊙Susp^ (l + n) X)
            (λ l → ⊙Susp^-+ l n)
            (+-comm m 1) ⟩
    ⊙Susp^-+ m 1 ◃∙
    ap (λ l → ⊙Susp^ l (⊙Susp^ n X)) (+-comm m 1) ◃∙
    ap ⊙Susp (Susp^-+ m n) ◃∙
    ap (λ k → ⊙Susp^ k X) (ap S (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 2 & 0 & contract ⟩
    ⊙Susp^-+ m 1 ◃∙
    ap (λ l → ⊙Susp^ l (⊙Susp^ n X)) (+-comm m 1) ◃∙
    idp ◃∙
    ap ⊙Susp (Susp^-+ m n) ◃∙
    ap (λ k → ⊙Susp^ k X) (ap S (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 0 & 3 & contract ⟩
    ⊙Susp^-comm m 1 ◃∙
    ap ⊙Susp (Susp^-+ m n) ◃∙
    ap (λ k → ⊙Susp^ k X) (ap S (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 2 & 1 & ∘-ap (λ k → ⊙Susp^ k X) S (+-comm m n) ∙
                   ap-∘ ⊙Susp (λ k → Susp^ k (de⊙ X)) (+-comm m n) ⟩
    ⊙Susp^-comm m 1 ◃∙
    ap ⊙Susp (Susp^-+ m n) ◃∙
    ap ⊙Susp (ap (λ k → Susp^ k (de⊙ X)) (+-comm m n)) ◃∙
    ! (ap ⊙Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 3 & 1 & !-ap ⊙Susp (Susp^-+ n m) ⟩
    ⊙Susp^-comm m 1 ◃∙
    ap ⊙Susp (Susp^-+ m n) ◃∙
    ap ⊙Susp (ap (λ k → Susp^ k (de⊙ X)) (+-comm m n)) ◃∙
    ap ⊙Susp (! (Susp^-+ n m)) ◃∎
      =ₛ⟨ 1 & 3 & ∙-ap-seq ⊙Susp (Susp^-comm-seq m n) ⟩
    ⊙Susp^-comm m 1 ◃∙
    ap ⊙Susp (Susp^-comm m n) ◃∎ ∎ₛ

  ⊙Susp^-comm-S-l : ∀ {i} (m n : ℕ) {X : Ptd i}
    → ⊙Susp^-comm (S m) n {X} ◃∎ =ₛ ap ⊙Susp (Susp^-comm m n) ◃∙ ⊙Susp^-comm 1 n {⊙Susp^ m X} ◃∎
  ⊙Susp^-comm-S-l m n {X} =
    ⊙Susp^-comm (S m) n {X} ◃∎
      =ₛ₁⟨ ! (⊙Susp^-comm-! n (S m) {X}) ⟩
    ! (⊙Susp^-comm n (S m) {X}) ◃∎
      =ₛ⟨ !-=ₛ (⊙Susp^-comm-S-r n m {X}) ⟩
    ! (ap ⊙Susp (Susp^-comm n m)) ◃∙
    ! (⊙Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 0 & 1 & !-ap ⊙Susp (Susp^-comm n m) ⟩
    ap ⊙Susp (! (Susp^-comm n m)) ◃∙
    ! (⊙Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 0 & 1 & ap (ap ⊙Susp) (Susp^-comm-! n m) ⟩
    ap ⊙Susp (Susp^-comm m n) ◃∙
    ! (⊙Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 1 & 1 & ⊙Susp^-comm-! n 1 ⟩
    ap ⊙Susp (Susp^-comm m n) ◃∙
    ⊙Susp^-comm 1 n ◃∎ ∎ₛ

  ⊙Susp^-comm-S-1 : ∀ {i} (m : ℕ) {X : Ptd i}
    → ⊙Susp^-comm (S m) 1 {X} == ap ⊙Susp (Susp^-comm m 1 {de⊙ X})
  ⊙Susp^-comm-S-1 m {X} = =ₛ-out $
    ⊙Susp^-comm (S m) 1 {X} ◃∎
      =ₛ⟨ ⊙Susp^-comm-S-l m 1 ⟩
    ap ⊙Susp (Susp^-comm m 1) ◃∙
    ⊙Susp^-comm 1 1 ◃∎
      =ₛ⟨ 1 & 1 & ⊙Susp^-comm-diag 1 ⟩
    ap ⊙Susp (Susp^-comm m 1) ◃∎ ∎ₛ

  ⊙Susp^-comm-1-S : ∀ {i} (n : ℕ) {X : Ptd i}
    → ⊙Susp^-comm 1 (S n) {X} == ap ⊙Susp (Susp^-comm 1 n {de⊙ X})
  ⊙Susp^-comm-1-S n {X} =
    ⊙Susp^-comm 1 (S n) {X}
      =⟨ ! (⊙Susp^-comm-! (S n) 1 {X}) ⟩
    ! (⊙Susp^-comm (S n) 1 {X})
      =⟨ ap ! (⊙Susp^-comm-S-1 n {X}) ⟩
    ! (ap ⊙Susp (Susp^-comm n 1 {de⊙ X}))
      =⟨ !-ap ⊙Susp (Susp^-comm n 1 {de⊙ X}) ⟩
    ap ⊙Susp (! (Susp^-comm n 1 {de⊙ X}))
      =⟨ ap (ap ⊙Susp) (Susp^-comm-! n 1 {de⊙ X}) ⟩
    ap ⊙Susp (Susp^-comm 1 n {de⊙ X}) =∎

  ⊙Susp^-comm-S-S : ∀ {i} (m n : ℕ) {X : Ptd i}
    → ⊙Susp^-comm (S m) (S n) {X} == ap ⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n)
  ⊙Susp^-comm-S-S m n {X} = =ₛ-out $
    ⊙Susp^-comm (S m) (S n) {X} ◃∎
      =ₛ⟨ ⊙Susp^-comm-S-l m (S n) ⟩
    ap ⊙Susp (Susp^-comm m (S n)) ◃∙
    ⊙Susp^-comm 1 (S n) ◃∎
      =ₛ₁⟨ 1 & 1 & ⊙Susp^-comm-1-S n ⟩
    ap ⊙Susp (Susp^-comm m (S n)) ◃∙
    ap ⊙Susp (Susp^-comm 1 n) ◃∎
      =ₛ⟨ ∙-ap-seq ⊙Susp (Susp^-comm m (S n) ◃∙ Susp^-comm 1 n ◃∎) ⟩
    ap ⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) ◃∎ ∎ₛ

abstract
  Susp^-+-natural : ∀ {i j} (m n : ℕ) {A : Type i} {B : Type j} (f : A → B)
    → coe (Susp^-+ m n) ∘ Susp^-fmap m (Susp^-fmap n f) ∼
      Susp^-fmap (m + n) f ∘ coe (Susp^-+ m n)
  Susp^-+-natural O n f sa = idp
  Susp^-+-natural (S m) n f sa =
    transport Susp (Susp^-+ m n) (Susp^-fmap (S m) (Susp^-fmap n f) sa)
      =⟨ transport-Susp (Susp^-+ m n) (Susp^-fmap (S m) (Susp^-fmap n f) sa) ⟩
    Susp-fmap (coe (Susp^-+ m n)) (Susp^-fmap (S m) (Susp^-fmap n f) sa)
      =⟨ ! (Susp-fmap-∘ (coe (Susp^-+ m n)) (Susp^-fmap m (Susp^-fmap n f)) sa) ⟩
    Susp-fmap (coe (Susp^-+ m n) ∘ Susp^-fmap m (Susp^-fmap n f)) sa
      =⟨ ap (λ f → Susp-fmap f sa) (λ= (Susp^-+-natural m n f)) ⟩
    Susp-fmap (Susp^-fmap (m + n) f ∘ coe (Susp^-+ m n)) sa
      =⟨ Susp-fmap-∘ (Susp^-fmap (m + n) f) (coe (Susp^-+ m n)) sa ⟩
    Susp^-fmap (S m + n) f (Susp-fmap (coe (Susp^-+ m n)) sa)
      =⟨ ap (Susp^-fmap (S m + n) f) (! (transport-Susp (Susp^-+ m n) sa)) ⟩
    Susp^-fmap (S m + n) f (transport Susp (Susp^-+ m n) sa) =∎

  ⊙Susp^-+-natural : ∀ {i j} (m n : ℕ) {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙coe (⊙Susp^-+ m n) ⊙∘ ⊙Susp^-fmap m (⊙Susp^-fmap n f) ==
      ⊙Susp^-fmap (m + n) f ⊙∘ ⊙coe (⊙Susp^-+ m n)
  ⊙Susp^-+-natural 0 n f = ⊙λ= (⊙∘-unit-l _)
  ⊙Susp^-+-natural (S m) n f =
    ⊙coe (ap ⊙Susp (Susp^-+ m n)) ⊙∘
    ⊙Susp^-fmap (S m) (⊙Susp^-fmap n f)
      =⟨ ap (_⊙∘ ⊙Susp^-fmap (S m) (⊙Susp^-fmap n f)) $
         ! (⊙transport-⊙coe ⊙Susp (Susp^-+ m n)) ∙
         ⊙transport-⊙Susp (Susp^-+ m n) ⟩
    ⊙Susp-fmap (coe (Susp^-+ m n)) ⊙∘
    ⊙Susp^-fmap (S m) (⊙Susp^-fmap n f)
      =⟨ ! $ ⊙Susp-fmap-∘ (coe (Susp^-+ m n)) (Susp^-fmap m (Susp^-fmap n (fst f))) ⟩
    ⊙Susp-fmap (coe (Susp^-+ m n) ∘ Susp^-fmap m (Susp^-fmap n (fst f)))
      =⟨ ap ⊙Susp-fmap (λ= (Susp^-+-natural m n (fst f))) ⟩
    ⊙Susp-fmap (Susp^-fmap (m + n) (fst f) ∘ coe (Susp^-+ m n))
      =⟨ ⊙Susp-fmap-∘ (Susp^-fmap (m + n) (fst f)) (coe (Susp^-+ m n)) ⟩
    ⊙Susp-fmap (Susp^-fmap (m + n) (fst f)) ⊙∘
    ⊙Susp-fmap (coe (Susp^-+ m n))
      =⟨ ap (⊙Susp-fmap (Susp^-fmap (m + n) (fst f)) ⊙∘_) $
         ! (⊙transport-⊙Susp (Susp^-+ m n)) ∙
         ⊙transport-⊙coe ⊙Susp (Susp^-+ m n) ⟩
    ⊙Susp-fmap (Susp^-fmap (m + n) (fst f)) ⊙∘
    ⊙coe (ap ⊙Susp (Susp^-+ m n)) =∎

  Susp^-+-natural' : ∀ {i j} (m n : ℕ) {A : Type i} {B : Type j} (f : A → B)
    → Susp^-fmap m (Susp^-fmap n f) ∘ coe (! (Susp^-+ m n)) ∼
      coe (! (Susp^-+ m n)) ∘ Susp^-fmap (m + n) f
  Susp^-+-natural' m n f sa =
    Susp^-fmap m (Susp^-fmap n f) (coe (! (Susp^-+ m n)) sa)
      =⟨ ap (λ p → coe p (Susp^-fmap m (Susp^-fmap n f) (coe (! (Susp^-+ m n)) sa))) $
         ! $ !-inv-r (Susp^-+ m n) ⟩
    coe (Susp^-+ m n ∙ ! (Susp^-+ m n))
        (Susp^-fmap m (Susp^-fmap n f) (coe (! (Susp^-+ m n)) sa))
      =⟨ coe-∙ (Susp^-+ m n) (! (Susp^-+ m n))
               (Susp^-fmap m (Susp^-fmap n f) (coe (! (Susp^-+ m n)) sa)) ⟩
    coe (! (Susp^-+ m n)) (coe (Susp^-+ m n) (Susp^-fmap m (Susp^-fmap n f) (coe (! (Susp^-+ m n)) sa)))
      =⟨ ap (coe (! (Susp^-+ m n))) $
         Susp^-+-natural m n f (coe (! (Susp^-+ m n)) sa) ⟩
    coe (! (Susp^-+ m n)) (Susp^-fmap (m + n) f (coe (Susp^-+ m n) (coe (! (Susp^-+ m n)) sa)))
      =⟨ ap (coe (! (Susp^-+ m n)) ∘ Susp^-fmap (m + n) f) $
         ! $ coe-∙ (! (Susp^-+ m n)) (Susp^-+ m n) sa ⟩
    coe (! (Susp^-+ m n)) (Susp^-fmap (m + n) f (coe (! (Susp^-+ m n) ∙ Susp^-+ m n) sa))
      =⟨ ap (λ p → coe (! (Susp^-+ m n)) (Susp^-fmap (m + n) f (coe p sa))) $
         !-inv-l (Susp^-+ m n) ⟩
    coe (! (Susp^-+ m n)) (Susp^-fmap (m + n) f sa) =∎

  ⊙Susp^-+-natural' : ∀ {i j} (m n : ℕ) {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙Susp^-fmap m (⊙Susp^-fmap n f) ⊙∘ ⊙coe (! (⊙Susp^-+ m n)) ==
      ⊙coe (! (⊙Susp^-+ m n)) ⊙∘ ⊙Susp^-fmap (m + n) f
  ⊙Susp^-+-natural' m n f =
    ⊙Susp^-fmap m (⊙Susp^-fmap n f) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (_⊙∘ ⊙coe (! (⊙Susp^-+ m n))) $
         ! $ ⊙λ= $ ⊙∘-unit-l (⊙Susp^-fmap m (⊙Susp^-fmap n f)) ⟩
    (⊙idf _ ⊙∘
     ⊙Susp^-fmap m (⊙Susp^-fmap n f)) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (_⊙∘ ⊙coe (! (⊙Susp^-+ m n))) $
         ap (_⊙∘ ⊙Susp^-fmap m (⊙Susp^-fmap n f)) $
         ap ⊙coe (! (!-inv-r (⊙Susp^-+ m n))) ∙
         =⊙∘-out (⊙coe-∙ (⊙Susp^-+ m n) (! (⊙Susp^-+ m n))) ⟩
    ((⊙coe (! (⊙Susp^-+ m n)) ⊙∘
      ⊙coe (⊙Susp^-+ m n)) ⊙∘
     ⊙Susp^-fmap m (⊙Susp^-fmap n f)) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (_⊙∘ ⊙coe (! (⊙Susp^-+ m n))) $ ⊙λ= $
         ⊙∘-assoc (⊙coe (! (⊙Susp^-+ m n)))
                  (⊙coe (⊙Susp^-+ m n))
                  (⊙Susp^-fmap m (⊙Susp^-fmap n f)) ⟩
    (⊙coe (! (⊙Susp^-+ m n)) ⊙∘
     ⊙coe (⊙Susp^-+ m n) ⊙∘
     ⊙Susp^-fmap m (⊙Susp^-fmap n f)) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (_⊙∘ ⊙coe (! (⊙Susp^-+ m n))) $
         ap (⊙coe (! (⊙Susp^-+ m n)) ⊙∘_) $
         ⊙Susp^-+-natural m n f ⟩
    (⊙coe (! (⊙Susp^-+ m n)) ⊙∘
     ⊙Susp^-fmap (m + n) f ⊙∘
     ⊙coe (⊙Susp^-+ m n)) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ⊙λ= $ ⊙∘-assoc
           (⊙coe (! (⊙Susp^-+ m n)))
           (⊙Susp^-fmap (m + n) f ⊙∘ ⊙coe (⊙Susp^-+ m n))
           (⊙coe (! (⊙Susp^-+ m n))) ⟩
    ⊙coe (! (⊙Susp^-+ m n)) ⊙∘
    (⊙Susp^-fmap (m + n) f ⊙∘
     ⊙coe (⊙Susp^-+ m n)) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (⊙coe (! (⊙Susp^-+ m n)) ⊙∘_) $ ⊙λ= $
         ⊙∘-assoc (⊙Susp^-fmap (m + n) f)
                  (⊙coe (⊙Susp^-+ m n))
                  (⊙coe (! (⊙Susp^-+ m n))) ⟩
    ⊙coe (! (⊙Susp^-+ m n)) ⊙∘
    ⊙Susp^-fmap (m + n) f ⊙∘
    ⊙coe (⊙Susp^-+ m n) ⊙∘
    ⊙coe (! (⊙Susp^-+ m n))
      =⟨ ap (⊙coe (! (⊙Susp^-+ m n)) ⊙∘_) $
         ap (⊙Susp^-fmap (m + n) f ⊙∘_) $
         ! (=⊙∘-out (⊙coe-∙ (! (⊙Susp^-+ m n)) (⊙Susp^-+ m n))) ∙
         ap ⊙coe (!-inv-l (⊙Susp^-+ m n)) ⟩
    ⊙coe (! (⊙Susp^-+ m n)) ⊙∘
    ⊙Susp^-fmap (m + n) f =∎

  Susp^-comm-natural : ∀ {i j} {A : Type i} {B : Type j} (m n : ℕ)
    (f : A → B)
    → coe (Susp^-comm m n) ∘ Susp^-fmap m (Susp^-fmap n f) ∼
      Susp^-fmap n (Susp^-fmap m f) ∘ coe (Susp^-comm m n)
  Susp^-comm-natural {A = A} {B = B} m n f s =
    coe (Susp^-comm m n) (Susp^-fmap m (Susp^-fmap n f) s)
      =⟨ coe-∙ (Susp^-+ m n)
               (ap (λ k → Susp^ k B) (+-comm m n) ∙ ! (Susp^-+ n m))
               (Susp^-fmap m (Susp^-fmap n f) s) ⟩
    coe (ap (λ k → Susp^ k B) (+-comm m n) ∙ ! (Susp^-+ n m))
        (coe (Susp^-+ m n) (Susp^-fmap m (Susp^-fmap n f) s))
      =⟨ ap (coe (ap (λ k → Susp^ k B) (+-comm m n) ∙ ! (Susp^-+ n m)))
            (Susp^-+-natural m n f s) ⟩
    coe (ap (λ k → Susp^ k B) (+-comm m n) ∙ ! (Susp^-+ n m))
        (Susp^-fmap (m + n) f (coe (Susp^-+ m n) s))
      =⟨ coe-∙ (ap (λ k → Susp^ k B) (+-comm m n))
               (! (Susp^-+ n m))
               (Susp^-fmap (m + n) f (coe (Susp^-+ m n) s)) ⟩
    coe (! (Susp^-+ n m))
        (transport (λ k → Susp^ k B) (+-comm m n)
          (Susp^-fmap (m + n) f (coe (Susp^-+ m n) s)))
      =⟨ ! $ ap (coe (! (Susp^-+ n m))) $
         app= (transp-naturality (λ {k} → Susp^-fmap k f) (+-comm m n))
              (coe (Susp^-+ m n) s) ⟩
    coe (! (Susp^-+ n m)) (Susp^-fmap (n + m) f
      (transport (λ k → Susp^ k A) (+-comm m n) (coe (Susp^-+ m n) s)))
      =⟨ ! $ Susp^-+-natural' n m f
           (transport (λ k → Susp^ k A) (+-comm m n) (coe (Susp^-+ m n) s)) ⟩
    Susp^-fmap n (Susp^-fmap m f)
      (coe (! (Susp^-+ n m)) (transport (λ k → Susp^ k A) (+-comm m n) (coe (Susp^-+ m n) s)))
      =⟨ ap (Susp^-fmap n (Susp^-fmap m f)) $ ! $
         coe-∙ (ap (λ k → Susp^ k A) (+-comm m n))
               (! (Susp^-+ n m))
               (coe (Susp^-+ m n) s) ⟩
    Susp^-fmap n (Susp^-fmap m f)
      (coe (ap (λ k → Susp^ k A) (+-comm m n) ∙ ! (Susp^-+ n m)) (coe (Susp^-+ m n) s))
      =⟨ ! $ ap (Susp^-fmap n (Susp^-fmap m f)) $
         coe-∙ (Susp^-+ m n) (ap (λ k → Susp^ k A) (+-comm m n) ∙ ! (Susp^-+ n m)) s ⟩
    Susp^-fmap n (Susp^-fmap m f) (coe (Susp^-comm m n) s) =∎

  ⊙Susp^-swap-natural : ∀ {i} {X Y : Ptd i} (m n : ℕ) (f : X ⊙→ Y)
    → ⊙Susp^-swap m n ◃⊙∘ ⊙Susp^-fmap m (⊙Susp^-fmap n f) ◃⊙idf
      =⊙∘
      ⊙Susp^-fmap n (⊙Susp^-fmap m f) ◃⊙∘ ⊙Susp^-swap m n ◃⊙idf
  ⊙Susp^-swap-natural {X = X} {Y = Y} m n f =
    ⊙Susp^-swap m n ◃⊙∘
    ⊙Susp^-fmap m (⊙Susp^-fmap n f) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙coe-∙ (⊙Susp^-+ m n)
                          (ap (λ k → ⊙Susp^ k Y) (+-comm m n) ∙ ! (⊙Susp^-+ n m)) ⟩
    ⊙coe (ap (λ k → ⊙Susp^ k Y) (+-comm m n) ∙ ! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙∘
    ⊙Susp^-fmap m (⊙Susp^-fmap n f) ◃⊙idf
      =⊙∘⟨ 1 & 2 & =⊙∘-in {gs = ⊙Susp^-fmap (m + n) f ◃⊙∘ ⊙coe (⊙Susp^-+ m n) ◃⊙idf} $
                   ⊙Susp^-+-natural m n f ⟩
    ⊙coe (ap (λ k → ⊙Susp^ k Y) (+-comm m n) ∙ ! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙Susp^-fmap (m + n) f ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙coe-∙ (ap (λ k → ⊙Susp^ k Y) (+-comm m n)) (! (⊙Susp^-+ n m)) ⟩
    ⊙coe (! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙coe (ap (λ k → ⊙Susp^ k Y) (+-comm m n)) ◃⊙∘
    ⊙Susp^-fmap (m + n) f ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ! $ ⊙transport-⊙coe (λ k → ⊙Susp^ k Y) (+-comm m n) ⟩
    ⊙coe (! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙transport (λ k → ⊙Susp^ k Y) (+-comm m n) ◃⊙∘
    ⊙Susp^-fmap (m + n) f ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘ (+-comm m n) (λ k → ⊙Susp^-fmap k f) ⟩
    ⊙coe (! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙Susp^-fmap (n + m) f ◃⊙∘
    ⊙transport (λ k → ⊙Susp^ k X) (+-comm m n) ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘₁⟨ 2 & 1 & ⊙transport-⊙coe (λ k → ⊙Susp^ k X) (+-comm m n) ⟩
    ⊙coe (! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙Susp^-fmap (n + m) f ◃⊙∘
    ⊙coe (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘⟨ 0 & 2 & =⊙∘-in {gs = ⊙Susp^-fmap n (⊙Susp^-fmap m f) ◃⊙∘
                                ⊙coe (! (⊙Susp^-+ n m)) ◃⊙idf} $
           ! $ ⊙Susp^-+-natural' n m f ⟩
    ⊙Susp^-fmap n (⊙Susp^-fmap m f) ◃⊙∘
    ⊙coe (! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙coe (ap (λ k → ⊙Susp^ k X) (+-comm m n)) ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙coe-∙ (ap (λ k → ⊙Susp^ k X) (+-comm m n)) (! (⊙Susp^-+ n m)) ⟩
    ⊙Susp^-fmap n (⊙Susp^-fmap m f) ◃⊙∘
    ⊙coe (ap (λ k → ⊙Susp^ k X) (+-comm m n) ∙ ! (⊙Susp^-+ n m)) ◃⊙∘
    ⊙coe (⊙Susp^-+ m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ $
           ⊙coe-∙ (⊙Susp^-+ m n)
                  (ap (λ k → ⊙Susp^ k X) (+-comm m n) ∙ ! (⊙Susp^-+ n m)) ⟩
    ⊙Susp^-fmap n (⊙Susp^-fmap m f) ◃⊙∘
    ⊙Susp^-swap m n ◃⊙idf ∎⊙∘

Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → Susp (Susp^ n A) ≃ Susp^ n (Susp A)
Susp^-Susp-split-iso O A = ide _
Susp^-Susp-split-iso (S n) A = Susp-emap (Susp^-Susp-split-iso n A)

⊙Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → ⊙Susp (Susp^ n A) ⊙≃ ⊙Susp^ n (⊙Susp A)
⊙Susp^-Susp-split-iso O A = ⊙ide _
⊙Susp^-Susp-split-iso (S n) A = ⊙Susp-emap (Susp^-Susp-split-iso n A)
