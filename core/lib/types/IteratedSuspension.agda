{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.FunctionSeq
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Suspension
open import lib.types.Truncation

module lib.types.IteratedSuspension where

Susp^ : ∀ {i} (n : ℕ) → Type i → Type i
Susp^ O X = X
Susp^ (S n) X = Susp (Susp^ n X)

Susp^-pt : ∀ {i} (n : ℕ) (A : Ptd i) → Susp^ n (de⊙ A)
Susp^-pt O A = pt A
Susp^-pt (S n) A = north

⊙Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
⊙Susp^ n X = ptd (Susp^ n (de⊙ X)) (Susp^-pt n X)

abstract
  Susp^-conn : ∀ {i} (n : ℕ) {A : Type i} {m : ℕ₋₂}
    {{_ : is-connected m A}} → is-connected (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
  Susp^-conn O = ⟨⟩
  Susp^-conn (S n) = Susp-conn (Susp^-conn n)

  ⊙Susp^-conn' : ∀ {i} (n : ℕ) {A : Type i}
    {{_ : is-connected 0 A}} → is-connected ⟨ n ⟩ (Susp^ n A)
  ⊙Susp^-conn' O = ⟨⟩
  ⊙Susp^-conn' (S n) = Susp-conn (⊙Susp^-conn' n)

module _ {i} {A : Type i} where
  maybe-Susp^-flip : ∀ (n : ℕ)
    → Bool
    → Susp^ n A → Susp^ n A
  maybe-Susp^-flip 0 _ = idf _
  maybe-Susp^-flip (S _) b = maybe-Susp-flip b

  Susp-fmap-maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → (n == 0 → b == false)
    → maybe-Susp^-flip (S n) b ∼ Susp-fmap (maybe-Susp^-flip n b)
  Susp-fmap-maybe-Susp^-flip O b h x =
    maybe-Susp^-flip 1 b x
      =⟨ ap (λ c → maybe-Susp^-flip 1 c x) (h idp) ⟩
    x
      =⟨ ! (Susp-fmap-idf A x) ⟩
    Susp-fmap (idf A) x =∎
  Susp-fmap-maybe-Susp^-flip (S n) true h x = ! (Susp-fmap-flip x)
  Susp-fmap-maybe-Susp^-flip (S n) false h x = ! (Susp-fmap-idf (Susp^ (S n) A) x)

module _ {i} {X : Ptd i} where

  ⊙maybe-Susp^-flip : ∀ (n : ℕ)
    → Bool
    → ⊙Susp^ n X ⊙→ ⊙Susp^ n X
  ⊙maybe-Susp^-flip 0 _ = ⊙idf _
  ⊙maybe-Susp^-flip (S n) b = ⊙maybe-Susp-flip (⊙Susp^ n X) b

  de⊙-⊙maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → fst (⊙maybe-Susp^-flip n b) == maybe-Susp^-flip n b
  de⊙-⊙maybe-Susp^-flip O b = idp
  de⊙-⊙maybe-Susp^-flip (S n) b = de⊙-⊙maybe-Susp-flip _ b

  ⊙maybe-Susp^-flip-false : ∀ (n : ℕ)
    → ⊙maybe-Susp^-flip n false == ⊙idf _
  ⊙maybe-Susp^-flip-false O = idp
  ⊙maybe-Susp^-flip-false (S n) = idp

  ⊙maybe-Susp^-flip-flip : ∀ (n : ℕ) (b c : Bool)
    → ⊙maybe-Susp^-flip n b ◃⊙∘ ⊙maybe-Susp^-flip n c ◃⊙idf
      =⊙∘
      ⊙maybe-Susp^-flip n (xor b c) ◃⊙idf
  ⊙maybe-Susp^-flip-flip 0     _ _ = =⊙∘-in idp
  ⊙maybe-Susp^-flip-flip (S n) b c = ⊙maybe-Susp-flip-flip (⊙Susp^ n X) b c

  ⊙Susp-fmap-maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → (n == 0 → b == false)
    → ⊙Susp-fmap (maybe-Susp^-flip n b) == ⊙maybe-Susp^-flip (S n) b
  ⊙Susp-fmap-maybe-Susp^-flip 0 b h =
    ⊙Susp-fmap (idf (de⊙ X))
      =⟨ =⊙∘-out (⊙Susp-fmap-idf _) ⟩
    ⊙idf _
      =⟨ ap (⊙maybe-Susp^-flip 1) (! (h idp)) ⟩
    ⊙maybe-Susp^-flip 1 b =∎
  ⊙Susp-fmap-maybe-Susp^-flip (S n) b h = ⊙Susp-fmap-maybe-Susp-flip b

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

Susp^-fmap : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j}
  → (A → B) → Susp^ n A → Susp^ n B
Susp^-fmap O f = f
Susp^-fmap (S n) f = Susp-fmap (Susp^-fmap n f)

⊙Susp^-fmap-pt : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  (f : X ⊙→ Y)
  → Susp^-fmap n (fst f) (pt (⊙Susp^ n X)) == pt (⊙Susp^ n Y)
⊙Susp^-fmap-pt O f = snd f
⊙Susp^-fmap-pt (S n) f = idp

⊙Susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Susp^ n X ⊙→ ⊙Susp^ n Y
⊙Susp^-fmap n f = Susp^-fmap n (fst f) , ⊙Susp^-fmap-pt n f

Susp^-fmap-idf : ∀ {i} (n : ℕ) (A : Type i)
  → Susp^-fmap n (idf A) == idf (Susp^ n A)
Susp^-fmap-idf O A = idp
Susp^-fmap-idf (S n) A = ↯ $
  Susp-fmap (Susp^-fmap n (idf A))
    =⟪ ap Susp-fmap (Susp^-fmap-idf n A) ⟫
  Susp-fmap (idf _)
    =⟪ λ= (Susp-fmap-idf _) ⟫
  idf (Susp^ (S n) A) ∎∎

transport-Susp^ : ∀ {i} {A B : Type i} (n : ℕ) (p : A == B)
  → transport (Susp^ n) p == Susp^-fmap n (coe p)
transport-Susp^ n idp = ! (Susp^-fmap-idf n _)

⊙Susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙Susp^-fmap n (⊙idf X) ◃⊙idf =⊙∘ ⊙idf-seq
⊙Susp^-fmap-idf O X = =⊙∘-in idp
⊙Susp^-fmap-idf (S n) X =
  ⊙Susp^-fmap (S n) (⊙idf X) ◃⊙idf
    =⊙∘₁⟨ ap ⊙Susp-fmap (Susp^-fmap-idf n (de⊙ X)) ⟩
  ⊙Susp-fmap (idf _) ◃⊙idf
    =⊙∘⟨ ⊙Susp-fmap-idf (Susp^ n (de⊙ X)) ⟩
  ⊙idf-seq ∎⊙∘

⊙transport-⊙Susp^ : ∀ {i} {X Y : Ptd i} (n : ℕ) (p : X == Y)
  → ⊙transport (⊙Susp^ n) p == ⊙Susp^-fmap n (⊙coe p)
⊙transport-⊙Susp^ n p@idp = ! (=⊙∘-out (⊙Susp^-fmap-idf n _))

Susp^-fmap-cst : ∀ {i j} (n : ℕ) {A : Type i} {Y : Ptd j}
  → Susp^-fmap n {A = A} (λ _ → pt Y) == (λ _ → pt (⊙Susp^ n Y))
Susp^-fmap-cst O = idp
Susp^-fmap-cst (S n) {A} {Y} = ↯ $
  Susp-fmap (Susp^-fmap n {A = A} (λ _ → pt Y))
    =⟪ ap Susp-fmap (Susp^-fmap-cst n) ⟫
  Susp-fmap (λ _ → pt (⊙Susp^ n Y))
    =⟪ λ= (Susp-fmap-cst (pt (⊙Susp^ n Y))) ⟫
  (λ _ → north) ∎∎

⊙Susp^-fmap-cst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙Susp^-fmap n (⊙cst {X = X} {Y = Y}) == ⊙cst
⊙Susp^-fmap-cst O = idp
⊙Susp^-fmap-cst (S n) = ap ⊙Susp-fmap (Susp^-fmap-cst n) ∙ ⊙Susp-fmap-cst

Susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B)
  → Susp^-fmap n (g ∘ f) == Susp^-fmap n g ∘ Susp^-fmap n f
Susp^-fmap-∘ O g f = idp
Susp^-fmap-∘ (S n) g f =
  Susp-fmap (Susp^-fmap n (g ∘ f))
    =⟨ ap Susp-fmap (Susp^-fmap-∘ n g f) ⟩
  Susp-fmap (Susp^-fmap n g ∘ Susp^-fmap n f)
    =⟨ λ= (Susp-fmap-∘ (Susp^-fmap n g) (Susp^-fmap n f)) ⟩
  Susp^-fmap (S n) g ∘ Susp^-fmap (S n) f =∎

⊙Susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Susp^-fmap n (g ⊙∘ f) == ⊙Susp^-fmap n g ⊙∘ ⊙Susp^-fmap n f
⊙Susp^-fmap-∘ O g f = idp
⊙Susp^-fmap-∘ (S n) g f =
  ap ⊙Susp-fmap (Susp^-fmap-∘ n (fst g) (fst f))
  ∙ ⊙Susp-fmap-∘ (Susp^-fmap n (fst g)) (Susp^-fmap n (fst f))

⊙Susp^-fmap-seq : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i}
  → X ⊙–→ Y
  → ⊙Susp^ n X ⊙–→ ⊙Susp^ n Y
⊙Susp^-fmap-seq n ⊙idf-seq = ⊙idf-seq
⊙Susp^-fmap-seq n (f ◃⊙∘ fs) = ⊙Susp^-fmap n f ◃⊙∘ ⊙Susp^-fmap-seq n fs

⊙Susp^-fmap-seq-∘ : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i} (fs : X ⊙–→ Y)
  → ⊙Susp^-fmap n (⊙compose fs) ◃⊙idf =⊙∘ ⊙Susp^-fmap-seq n fs
⊙Susp^-fmap-seq-∘ n ⊙idf-seq = ⊙Susp^-fmap-idf n _
⊙Susp^-fmap-seq-∘ n (f ◃⊙∘ fs) = =⊙∘-in $
  ⊙Susp^-fmap n (f ⊙∘ ⊙compose fs)
    =⟨ ⊙Susp^-fmap-∘ n f (⊙compose fs) ⟩
  ⊙Susp^-fmap n f ⊙∘ ⊙Susp^-fmap n (⊙compose fs)
    =⟨ ap (⊙Susp^-fmap n f ⊙∘_) (=⊙∘-out (⊙Susp^-fmap-seq-∘ n fs)) ⟩
  ⊙Susp^-fmap n f ⊙∘ ⊙compose (⊙Susp^-fmap-seq n fs) =∎

⊙Susp^-fmap-seq-=⊙∘ : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i} {fs gs : X ⊙–→ Y}
  → fs =⊙∘ gs
  → ⊙Susp^-fmap-seq n fs =⊙∘ ⊙Susp^-fmap-seq n gs
⊙Susp^-fmap-seq-=⊙∘ n {fs = fs} {gs = gs} p =
  ⊙Susp^-fmap-seq n fs
    =⊙∘⟨ !⊙∘ $ ⊙Susp^-fmap-seq-∘ n fs ⟩
  ⊙Susp^-fmap n (⊙compose fs) ◃⊙idf
    =⊙∘₁⟨ ap (⊙Susp^-fmap n) (=⊙∘-out p) ⟩
  ⊙Susp^-fmap n (⊙compose gs) ◃⊙idf
    =⊙∘⟨ ⊙Susp^-fmap-seq-∘ n gs ⟩
  ⊙Susp^-fmap-seq n gs ∎⊙∘

Susp^-fmap-Susp-flip : ∀ {i} (m : ℕ) {A : Type i} (s : Susp^ (S m) (Susp A))
  → Susp^-fmap (S m) Susp-flip s == Susp-flip s
Susp^-fmap-Susp-flip O {A} s = Susp-fmap-flip s
Susp^-fmap-Susp-flip (S m) {A} s =
  Susp^-fmap (S (S m)) Susp-flip s
    =⟨ ap (λ f → Susp-fmap f s) (λ= (Susp^-fmap-Susp-flip m)) ⟩
  Susp-fmap Susp-flip s
    =⟨ Susp-fmap-flip s ⟩
  Susp-flip s =∎

abstract
  ⊙Susp^-fmap-⊙Susp-flip : ∀ {i} (m : ℕ) {X : Ptd i}
    → ⊙Susp^-fmap (S m) (⊙Susp-flip X) == ⊙Susp-flip (⊙Susp^ m (⊙Susp (de⊙ X)))
  ⊙Susp^-fmap-⊙Susp-flip 0 {X} = ⊙Susp-fmap-Susp-flip
  ⊙Susp^-fmap-⊙Susp-flip (S m) {X} =
    ⊙Susp^-fmap (S (S m)) (⊙Susp-flip X)
      =⟨ ap ⊙Susp-fmap (λ= (Susp^-fmap-Susp-flip m)) ⟩
    ⊙Susp-fmap Susp-flip
      =⟨ ⊙Susp-fmap-Susp-flip ⟩
    ⊙Susp-flip (⊙Susp^ (S m) (⊙Susp (de⊙ X))) =∎

  {-
  ⊙Susp^-fmap-⊙maybe-Susp-flip : ∀ {i} (m : ℕ) (b : Bool) {X : Ptd i}
    → ⊙Susp^-fmap (S m) (⊙maybe-Susp-flip X b) == ⊙maybe-Susp-flip (⊙Susp^ m (⊙Susp (de⊙ X))) b
  ⊙Susp^-fmap-⊙maybe-Susp-flip m true {X} = ⊙Susp^-fmap-⊙Susp-flip m {X}
  ⊙Susp^-fmap-⊙maybe-Susp-flip m false {X} = =⊙∘-out $ ⊙Susp^-fmap-idf (S m) (⊙Susp (de⊙ X))
  -}

  ⊙maybe-Susp^-flip-natural : ∀ {i} {j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    (n : ℕ) (b : Bool)
    → ⊙Susp^-fmap n f ⊙∘ ⊙maybe-Susp^-flip n b ==
      ⊙maybe-Susp^-flip n b ⊙∘ ⊙Susp^-fmap n f
  ⊙maybe-Susp^-flip-natural f O b = ! (⊙λ= (⊙∘-unit-l f))
  ⊙maybe-Susp^-flip-natural f (S n) b = ⊙maybe-Susp-flip-natural (⊙Susp^-fmap n f) b

  ⊙maybe-Susp^-flip-natural-=⊙∘ : ∀ {i} {X Y : Ptd i} (f : X ⊙→ Y)
    (n : ℕ) (b : Bool)
    → ⊙Susp^-fmap n f ◃⊙∘
      ⊙maybe-Susp^-flip n b ◃⊙idf
      =⊙∘
      ⊙maybe-Susp^-flip n b ◃⊙∘
      ⊙Susp^-fmap n f ◃⊙idf
  ⊙maybe-Susp^-flip-natural-=⊙∘ f n b =
    =⊙∘-in (⊙maybe-Susp^-flip-natural f n b)

abstract

  ⊙Susp^-comm-flip : ∀ {i} (m n : ℕ) (X : Ptd i)
    → ⊙Susp^-fmap n (⊙Susp-flip (⊙Susp^ m X)) ◃⊙∘
      ⊙coe (⊙Susp^-comm (S m) n {X}) ◃⊙idf
      =⊙∘
      ⊙coe (⊙Susp^-comm (S m) n {X}) ◃⊙∘
      ⊙Susp-flip (⊙Susp^ m (⊙Susp^ n X)) ◃⊙idf
  ⊙Susp^-comm-flip m O X =
    ⊙Susp-flip (⊙Susp^ m X) ◃⊙∘
    ⊙coe (⊙Susp^-comm (S m) 0) ◃⊙idf
      =⊙∘⟨ 1 & 1 & =⊙∘-in {gs = ⊙idf-seq} $ ap ⊙coe (⊙Susp^-comm-0-r (S m) X) ⟩
    ⊙Susp-flip (⊙Susp^ m X) ◃⊙idf
      =⊙∘⟨ 0 & 0 & =⊙∘-in {gs = ⊙coe (⊙Susp^-comm (S m) O) ◃⊙idf} $
                   ! $ ap ⊙coe (⊙Susp^-comm-0-r (S m) X) ⟩
    ⊙coe (⊙Susp^-comm (S m) O) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ O X)) ◃⊙idf ∎⊙∘
  ⊙Susp^-comm-flip m (S n) X =
    ⊙Susp^-fmap (S n) (⊙Susp-flip (⊙Susp^ m X)) ◃⊙∘
    ⊙coe (⊙Susp^-comm (S m) (S n)) ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ⊙Susp^-fmap-⊙Susp-flip n {⊙Susp^ m X} ⟩
    ⊙Susp-flip (⊙Susp^ n (⊙Susp (Susp^ m (de⊙ X)))) ◃⊙∘
    ⊙coe (⊙Susp^-comm (S m) (S n)) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & p ⟩
    ⊙Susp-flip (⊙Susp^ n (⊙Susp (Susp^ m (de⊙ X)))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) ∙ ⊙Susp^-comm 1 n))) ◃⊙idf
      =⊙∘⟨ =⊙∘-in {gs = ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) {X} ∙ ⊙Susp^-comm 1 n {⊙Susp^ m X}))) ◃⊙∘
                        ⊙Susp-flip (⊙Susp^ m (⊙Susp (Susp^ n (de⊙ X)))) ◃⊙idf} $
           ⊙Susp-flip-natural (⊙coe (⊙Susp^-comm m (S n) ∙ ⊙Susp^-comm 1 n)) ⟩
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) {X} ∙ ⊙Susp^-comm 1 n {⊙Susp^ m X}))) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp (Susp^ n (de⊙ X)))) ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ! p ⟩
    ⊙coe (⊙Susp^-comm (S m) (S n)) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ (S n) X)) ◃⊙idf ∎⊙∘
    where
    p : ⊙coe (⊙Susp^-comm (S m) (S n) {X}) ==
        ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) {X} ∙ ⊙Susp^-comm 1 n {⊙Susp^ m X})))
    p =
      ap ⊙coe (⊙Susp^-comm-S-S m n) ∙
      ! (⊙transport-⊙coe ⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) ∙
      ⊙transport-⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) ∙
      ap (⊙Susp-fmap ∘ coe) (ap2 _∙_ (! (de⊙-⊙Susp^-comm m (S n) {X}))
                                     (! (de⊙-⊙Susp^-comm 1 n {⊙Susp^ m X}))) ∙
      ap (⊙Susp-fmap ∘ coe) (∙-ap de⊙ (⊙Susp^-comm m (S n)) (⊙Susp^-comm 1 n))

  ⊙maybe-Susp^-flip-⊙Susp^-comm : ∀ {i} (X : Ptd i) (m n : ℕ) (b : Bool)
    → ⊙Susp^-fmap n (⊙maybe-Susp^-flip m b) ◃⊙∘
      ⊙coe (⊙Susp^-comm m n {X}) ◃⊙idf
      =⊙∘
      ⊙coe (⊙Susp^-comm m n {X}) ◃⊙∘
      ⊙maybe-Susp^-flip m b ◃⊙idf
  ⊙maybe-Susp^-flip-⊙Susp^-comm X O n b =
    ⊙Susp^-fmap n (⊙idf X) ◃⊙∘
    ⊙coe (⊙Susp^-comm 0 n) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙Susp^-fmap-idf n X ⟩
    ⊙coe (⊙Susp^-comm 0 n) ◃⊙idf
      =⊙∘⟨ 1 & 0 & ⊙contract ⟩
    ⊙coe (⊙Susp^-comm 0 n) ◃⊙∘
    ⊙idf (⊙Susp^ n X) ◃⊙idf ∎⊙∘
  ⊙maybe-Susp^-flip-⊙Susp^-comm X (S m) n true = ⊙Susp^-comm-flip m n X
  ⊙maybe-Susp^-flip-⊙Susp^-comm X (S m) n false =
    ⊙Susp^-fmap n (⊙idf (⊙Susp^ (S m) X)) ◃⊙∘
    ⊙coe (⊙Susp^-comm (S m) n) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙Susp^-fmap-idf n (⊙Susp^ (S m) X) ⟩
    ⊙coe (⊙Susp^-comm (S m) n) ◃⊙idf
      =⊙∘⟨ 1 & 0 & ⊙contract ⟩
    ⊙coe (⊙Susp^-comm (S m) n) ◃⊙∘
    ⊙idf (⊙Susp^ (S m) (⊙Susp^ n X)) ◃⊙idf ∎⊙∘

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

module _ {i} (A : Type i) (m : ℕ₋₂) where

  Susp^-Trunc-swap : ∀ (n : ℕ)
    → Susp^ n (Trunc m A)
    → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
  Susp^-Trunc-swap O = idf _
  Susp^-Trunc-swap (S n) =
    Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) ∘
    Susp-fmap (Susp^-Trunc-swap n)

  private
    to : ∀ n → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n (Trunc m A)) → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
    to n = Trunc-rec {{Trunc-level}} (Susp^-Trunc-swap n)

    from : ∀ n → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A) → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n (Trunc m A))
    from n = Trunc-fmap (Susp^-fmap n [_])

    abstract
      from-Susp^-Trunc-swap : ∀ n → from n ∘ Susp^-Trunc-swap n ∼ [_]
      from-Susp^-Trunc-swap O =
        Trunc-elim
          {P = λ s → from 0 (Susp^-Trunc-swap 0 s) == [ s ]}
          {{λ s → =-preserves-level Trunc-level}}
          (λ a → idp)
      from-Susp^-Trunc-swap (S n) x =
        (from (S n) $
         Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Susp^-Trunc-swap n) x)
          =⟨ ! $ Susp-Trunc-swap-natural (Susp^-fmap n [_]) (⟨ n ⟩₋₂ +2+ m) $
             Susp-fmap (Susp^-Trunc-swap n) x ⟩
        (Susp-Trunc-swap (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Trunc-fmap (Susp^-fmap n [_])) $
         Susp-fmap (Susp^-Trunc-swap n) x)
          =⟨ ap (Susp-Trunc-swap (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m)) $
             ! $ Susp-fmap-∘ (Trunc-fmap (Susp^-fmap n [_])) (Susp^-Trunc-swap n) x ⟩
        (Susp-Trunc-swap (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (from n ∘ Susp^-Trunc-swap n) x)
          =⟨ ap (Susp-Trunc-swap (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m)) $
             ap (λ f → Susp-fmap f x) (λ= (from-Susp^-Trunc-swap n)) ⟩
        Susp-Trunc-swap (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m) (Susp-fmap [_] x)
          =⟨ Susp-Trunc-swap-Susp-fmap-trunc (Susp^ n (Trunc m A)) (⟨ n ⟩₋₂ +2+ m) x ⟩
        [ x ] =∎

      from-to : ∀ n → from n ∘ to n ∼ idf _
      from-to n =
        Trunc-elim
          {P = λ t → from n (to n t) == t}
          {{λ t → =-preserves-level Trunc-level}}
          (from-Susp^-Trunc-swap n)

      Susp^-Trunc-swap-Susp^-fmap-trunc : ∀ n →
        Susp^-Trunc-swap n ∘ Susp^-fmap n [_] ∼ [_]
      Susp^-Trunc-swap-Susp^-fmap-trunc 0 s = idp
      Susp^-Trunc-swap-Susp^-fmap-trunc (S n) s =
        (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Susp^-Trunc-swap n) $
         Susp^-fmap (S n) [_] s)
          =⟨ ap (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m)) $
             ! $ Susp-fmap-∘ (Susp^-Trunc-swap n) (Susp^-fmap n [_]) s ⟩
        (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Susp^-Trunc-swap n ∘ Susp^-fmap n [_]) s)
          =⟨ ap (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m)) $
             app= (ap Susp-fmap (λ= (Susp^-Trunc-swap-Susp^-fmap-trunc n))) s ⟩
        Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) (Susp-fmap [_] s)
          =⟨ Susp-Trunc-swap-Susp-fmap-trunc (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) s ⟩
        [ s ] =∎

      to-from : ∀ n → to n ∘ from n ∼ idf _
      to-from n = Trunc-elim {{λ t → =-preserves-level Trunc-level}}
                             (Susp^-Trunc-swap-Susp^-fmap-trunc n)

  Susp^-Trunc-equiv : ∀ (n : ℕ)
    → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n (Trunc m A)) ≃ Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
  Susp^-Trunc-equiv n = equiv (to n) (from n) (to-from n) (from-to n)

module _ {i} (X : Ptd i) (m : ℕ₋₂) where

  Susp^-Trunc-swap-pt : ∀ (n : ℕ)
    → Susp^-Trunc-swap (de⊙ X) m n (pt (⊙Susp^ n (⊙Trunc m X))) ==
      pt (⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X))
  Susp^-Trunc-swap-pt O = idp
  Susp^-Trunc-swap-pt (S n) = idp

  ⊙Susp^-Trunc-swap : ∀ (n : ℕ)
    → ⊙Susp^ n (⊙Trunc m X) ⊙→ ⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)
  ⊙Susp^-Trunc-swap n = Susp^-Trunc-swap (de⊙ X) m n , Susp^-Trunc-swap-pt n

  ⊙Susp^-⊙Trunc-equiv : ∀ (n : ℕ)
    → ⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n (⊙Trunc m X)) ⊙≃ ⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)
  ⊙Susp^-⊙Trunc-equiv n =
    ⊙to , snd (Susp^-Trunc-equiv (de⊙ X) m n)
    where
    ⊙to : ⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n (⊙Trunc m X))
       ⊙→ ⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)
    ⊙to = ⊙Trunc-rec {{Trunc-level}} (⊙Susp^-Trunc-swap n)

  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → ⊙Susp^-Trunc-swap n ◃⊙∘
      ⊙maybe-Susp^-flip n b ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙maybe-Susp^-flip n b) ◃⊙∘
      ⊙Susp^-Trunc-swap n ◃⊙idf
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip O b =
    =⊙∘-in (! (⊙λ= ⊙Trunc-fmap-⊙idf))
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip (S n) true =
    ⊙Susp^-Trunc-swap (S n) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ n (⊙Trunc m X)) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙expand $
           ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
           ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf ⟩
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ n (⊙Trunc m X)) ◃⊙idf
      =⊙∘⟨ 1 & 2 & =⊙∘-in
           {gs = ⊙Susp-flip (⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)) ◃⊙∘
                 ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf} $
           ! $ ⊙Susp-flip-natural (⊙Susp^-Trunc-swap n) ⟩
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-flip (⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙Susp-Trunc-swap-⊙Susp-flip (⟨ n ⟩₋₂ +2+ m) ⟩
    ⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙contract ⟩
    ⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp^-Trunc-swap (S n) ◃⊙idf ∎⊙∘
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip (S n) false =
    ⊙Susp^-Trunc-swap (S n) ◃⊙∘
    ⊙idf _ ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand ⊙idf-seq ⟩
    ⊙Susp^-Trunc-swap (S n) ◃⊙idf
      =⊙∘₁⟨ 0 & 0 & ! (⊙λ= ⊙Trunc-fmap-⊙idf) ⟩
    ⊙Trunc-fmap (⊙idf (⊙Susp (de⊙ (⊙Susp^ n X)))) ◃⊙∘
    ⊙Susp^-Trunc-swap (S n) ◃⊙idf ∎⊙∘

module _ {i} {X Y : Ptd i} (f : X ⊙→ Y) (m : ℕ₋₂) where

  ⊙Susp^-Trunc-swap-natural : ∀ (n : ℕ)
    → ⊙Susp^-Trunc-swap Y m n ◃⊙∘
      ⊙Susp^-fmap n (⊙Trunc-fmap f) ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap n f) ◃⊙∘
      ⊙Susp^-Trunc-swap X m n ◃⊙idf
  ⊙Susp^-Trunc-swap-natural O = =⊙∘-in (⊙λ= (⊙∘-unit-l _))
  ⊙Susp^-Trunc-swap-natural (S n) =
    ⊙Susp^-Trunc-swap Y m (S n) ◃⊙∘
    ⊙Susp^-fmap (S n) (⊙Trunc-fmap f) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙expand $
           ⊙Susp-Trunc-swap (Susp^ n (de⊙ Y)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
           ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ Y) m n) ◃⊙idf ⟩
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ Y)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ Y) m n) ◃⊙∘
    ⊙Susp^-fmap (S n) (⊙Trunc-fmap f) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙Susp-fmap-seq-=⊙∘ $
           de⊙-seq-=⊙∘ $ ⊙Susp^-Trunc-swap-natural n ⟩
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ Y)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Trunc-fmap (Susp^-fmap n (fst f))) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 0 & 2 & =⊙∘-in
           {gs = ⊙Trunc-fmap (⊙Susp-fmap (Susp^-fmap n (fst f))) ◃⊙∘
                 ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙idf} $
           ⊙Susp-Trunc-swap-natural (Susp^-fmap n (fst f)) (⟨ n ⟩₋₂ +2+ m) ⟩
    ⊙Trunc-fmap (⊙Susp-fmap (Susp^-fmap n (fst f))) ◃⊙∘
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙contract ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap (S n) f) ◃⊙∘
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙idf ∎⊙∘

  ⊙Susp^-⊙Trunc-equiv-natural : ∀ (n : ℕ)
    → ⊙–> (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap n (⊙Trunc-fmap f)) ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap n f) ◃⊙∘
      ⊙–> (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙idf
  ⊙Susp^-⊙Trunc-equiv-natural n = =⊙∘-in $
    ⊙–> (⊙Susp^-⊙Trunc-equiv Y m n) ⊙∘
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙Trunc-fmap f))
      =⟨ ⊙Trunc-rec-⊙Trunc-fmap {{Trunc-level}}
           (⊙Susp^-Trunc-swap Y m n)
           (⊙Susp^-fmap n (⊙Trunc-fmap f)) ⟩
    ⊙Trunc-rec {{Trunc-level}} (⊙Susp^-Trunc-swap Y m n ⊙∘ ⊙Susp^-fmap n (⊙Trunc-fmap f))
      =⟨ ap (⊙Trunc-rec {{Trunc-level}}) $
         =⊙∘-out $ ⊙Susp^-Trunc-swap-natural n ⟩
    ⊙Trunc-rec {{Trunc-level}} (⊙Trunc-fmap (⊙Susp^-fmap n f) ⊙∘ ⊙Susp^-Trunc-swap X m n)
      =⟨ ⊙Trunc-rec-post-⊙∘ {{Trunc-level}} {{Trunc-level}}
           (⊙Trunc-fmap (⊙Susp^-fmap n f))
           (⊙Susp^-Trunc-swap X m n) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n f) ⊙∘ ⊙–> (⊙Susp^-⊙Trunc-equiv X m n) =∎

  ⊙Susp^-⊙Trunc-equiv-natural' : ∀ (n : ℕ)
    → ⊙<– (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap n f) ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap n (⊙Trunc-fmap f)) ◃⊙∘
      ⊙<– (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙idf
  ⊙Susp^-⊙Trunc-equiv-natural' n =
    ⊙<– (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-fmap n f) ◃⊙idf
      =⊙∘⟨ 2 & 0 & !⊙∘ $ ⊙<–-inv-r-=⊙∘ (⊙Susp^-⊙Trunc-equiv X m n) ⟩
    ⊙<– (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-fmap n f) ◃⊙∘
    ⊙–> (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙∘
    ⊙<– (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙Susp^-⊙Trunc-equiv-natural n ⟩
    ⊙<– (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
    ⊙–> (⊙Susp^-⊙Trunc-equiv Y m n) ◃⊙∘
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙Trunc-fmap f)) ◃⊙∘
    ⊙<– (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (⊙Susp^-⊙Trunc-equiv Y m n) ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap n (⊙Trunc-fmap f)) ◃⊙∘
    ⊙<– (⊙Susp^-⊙Trunc-equiv X m n) ◃⊙idf ∎⊙∘

Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → Susp (Susp^ n A) ≃ Susp^ n (Susp A)
Susp^-Susp-split-iso O A = ide _
Susp^-Susp-split-iso (S n) A = Susp-emap (Susp^-Susp-split-iso n A)

⊙Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → ⊙Susp (Susp^ n A) ⊙≃ ⊙Susp^ n (⊙Susp A)
⊙Susp^-Susp-split-iso O A = ⊙ide _
⊙Susp^-Susp-split-iso (S n) A = ⊙Susp-emap (Susp^-Susp-split-iso n A)

⊙Sphere : (n : ℕ) → Ptd₀
⊙Sphere n = ⊙Susp^ n ⊙Bool

Sphere : (n : ℕ) → Type₀
Sphere n = de⊙ (⊙Sphere n)

abstract
  instance
    Sphere-conn : ∀ (n : ℕ) → is-connected ⟨ n ⟩₋₁ (Sphere n)
    Sphere-conn 0 = inhab-conn true
    Sphere-conn (S n) = Susp-conn (Sphere-conn n)

-- favonia: [S¹] has its own elim rules in Circle.agda.
⊙S⁰ = ⊙Sphere 0
⊙S¹ = ⊙Sphere 1
⊙S² = ⊙Sphere 2
⊙S³ = ⊙Sphere 3
S⁰ = Sphere 0
S¹ = Sphere 1
S² = Sphere 2
S³ = Sphere 3
