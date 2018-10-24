{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.Nat
open import lib.types.Paths
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
  maybe-Susp^-flip (S _) true  = Susp-flip
  maybe-Susp^-flip (S _) false = idf _

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

Susp^-+ : ∀ {i} (m n : ℕ) {A : Type i}
  → Susp^ m (Susp^ n A) == Susp^ (m + n) A
Susp^-+ O n = idp
Susp^-+ (S m) n = ap Susp (Susp^-+ m n)

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

Susp^-+-pt : ∀ {i} (m n : ℕ) {X : Ptd i}
  → Susp^-pt m (⊙Susp^ n X) == Susp^-pt (m + n) X [ idf _ ↓ Susp^-+ m n ]
Susp^-+-pt O n = idp
Susp^-+-pt (S m) n =
  ↓-ap-in (idf _) Susp (apd (λ A → north {A = A}) (Susp^-+ m n))

⊙Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) == ⊙Susp^ (m + n) X
⊙Susp^-+ m n {X} = ptd= (Susp^-+ m n {de⊙ X}) (Susp^-+-pt m n)

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

abstract
  Susp^-comm-diag : ∀ {i} (m : ℕ) {A : Type i}
    → Susp^-comm m m {A} ◃∎ =ₛ []
  Susp^-comm-diag m {A} =
    ↯ (Susp^-comm-seq m m {A}) ◃∎
      =ₛ⟨ expand (Susp^-comm-seq m m {A}) ⟩
    Susp^-+ m m ◃∙
    ap (λ k → Susp^ k A) (+-comm m m) ◃∙
    ! (Susp^-+ m m) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → Susp^ k A)) (set-path ℕ-level (+-comm m m) idp) ⟩
    Susp^-+ m m ◃∙
    idp ◃∙
    ! (Susp^-+ m m) ◃∎
      =ₛ⟨ 1 & 1 & expand [] ⟩
    Susp^-+ m m ◃∙
    ! (Susp^-+ m m) ◃∎
      =ₛ⟨ seq-!-inv-r (Susp^-+ m m ◃∎) ⟩
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

  Susp^-comm-0-r : ∀ {i} (m : ℕ) (A : Type i)
    → Susp^-comm m 0 {A} == idp
  Susp^-comm-0-r m A = =ₛ-out $
    Susp^-+ m 0 ◃∙
    ap (λ k → Susp^ k A) (+-comm m 0) ◃∙
    ! (Susp^-+ 0 m) ◃∎
      =ₛ⟨ 2 & 1 & expand [] ⟩
    Susp^-+ m 0 ◃∙
    ap (λ k → Susp^ k A) (+-comm m 0) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ k → Susp^ k A)) $
                  set-path ℕ-level (+-comm m 0) (+-unit-r m) ⟩
    Susp^-+ m 0 ◃∙
    ap (λ k → Susp^ k A) (+-unit-r m) ◃∎
      =ₛ⟨ Susp^-+-0-r m ⟩
    [] ∎ₛ

  Susp^-comm-0-l : ∀ {i} (n : ℕ) (A : Type i)
    → Susp^-comm 0 n {A} == idp
  Susp^-comm-0-l n A =
    Susp^-comm 0 n {A}
      =⟨ ! (Susp^-comm-! n 0 {A}) ⟩
    ! (Susp^-comm n 0 {A})
      =⟨ ap ! (Susp^-comm-0-r n A) ⟩
    idp =∎

  Susp^-comm-S-r : ∀ {i} (m n : ℕ) {A : Type i}
    → Susp^-comm m (S n) {A} ◃∎ =ₛ Susp^-comm m 1 ◃∙ ap Susp (Susp^-comm m n) ◃∎
  Susp^-comm-S-r m n {A} =
    Susp^-comm m (S n) {A} ◃∎
      =ₛ⟨ expand (Susp^-comm-seq m (S n) {A}) ⟩
    Susp^-+ m (S n) ◃∙
    ap (λ k → Susp^ k A) (+-comm m (S n)) ◃∙
    ! (Susp^-+ (S n) m) ◃∎
      =ₛ⟨ 0 & 0 & contract ⟩
    idp ◃∙
    Susp^-+ m (S n) ◃∙
    ap (λ k → Susp^ k A) (+-comm m (S n)) ◃∙
    ! (Susp^-+ (S n) m) ◃∎
      =ₛ⟨ 0 & 2 & Susp^-+-assoc-coh m 1 n ⟩
    Susp^-+ m 1 ◃∙
    Susp^-+ (m + 1) n ◃∙
    ap (λ k → Susp^ k A) (+-assoc m 1 n) ◃∙
    ap (λ k → Susp^ k A) (+-comm m (S n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 2 & 2 & ap-seq-=ₛ (λ k → Susp^ k A) $
          =ₛ-in {s = +-assoc m 1 n ◃∙ +-comm m (S n) ◃∎}
                {t = ap (_+ n) (+-comm m 1) ◃∙ ap S (+-comm m n) ◃∎} $
          set-path ℕ-level _ _ ⟩
    Susp^-+ m 1 ◃∙
    Susp^-+ (m + 1) n ◃∙
    ap (λ k → Susp^ k A) (ap (_+ n) (+-comm m 1)) ◃∙
    ap (λ k → Susp^ k A) (ap S (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 2 & 1 & ∘-ap (λ k → Susp^ k A) (_+ n) (+-comm m 1) ⟩
    Susp^-+ m 1 ◃∙
    Susp^-+ (m + 1) n ◃∙
    ap (λ k → Susp^ (k + n) A) (+-comm m 1) ◃∙
    ap (λ k → Susp^ k A) (ap S (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 1 & 2 & !ₛ $ homotopy-naturality
            (λ l → Susp^ l (Susp^ n A))
            (λ l → Susp^ (l + n) A)
            (λ l → Susp^-+ l n)
            (+-comm m 1) ⟩
    Susp^-+ m 1 ◃∙
    ap (λ l → Susp^ l (Susp^ n A)) (+-comm m 1) ◃∙
    ap Susp (Susp^-+ m n) ◃∙
    ap (λ k → Susp^ k A) (ap S (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 2 & 0 & contract ⟩
    Susp^-+ m 1 ◃∙
    ap (λ l → Susp^ l (Susp^ n A)) (+-comm m 1) ◃∙
    idp ◃∙
    ap Susp (Susp^-+ m n) ◃∙
    ap (λ k → Susp^ k A) (ap S (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ⟨ 0 & 3 & contract ⟩
    Susp^-comm m 1 ◃∙
    ap Susp (Susp^-+ m n) ◃∙
    ap (λ k → Susp^ k A) (ap S (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 2 & 1 & ∘-ap (λ k → Susp^ k A) S (+-comm m n) ∙
                   ap-∘ Susp (λ k → Susp^ k A) (+-comm m n) ⟩
    Susp^-comm m 1 ◃∙
    ap Susp (Susp^-+ m n) ◃∙
    ap Susp (ap (λ k → Susp^ k A) (+-comm m n)) ◃∙
    ! (ap Susp (Susp^-+ n m)) ◃∎
      =ₛ₁⟨ 3 & 1 & !-ap Susp (Susp^-+ n m) ⟩
    Susp^-comm m 1 ◃∙
    ap Susp (Susp^-+ m n) ◃∙
    ap Susp (ap (λ k → Susp^ k A) (+-comm m n)) ◃∙
    ap Susp (! (Susp^-+ n m)) ◃∎
      =ₛ⟨ 1 & 3 & ∙-ap-seq Susp (Susp^-comm-seq m n) ⟩
    Susp^-comm m 1 ◃∙
    ap Susp (Susp^-comm m n) ◃∎ ∎ₛ

  Susp^-comm-S-l : ∀ {i} (m n : ℕ) {A : Type i}
    → Susp^-comm (S m) n {A} ◃∎ =ₛ ap Susp (Susp^-comm m n) ◃∙ Susp^-comm 1 n ◃∎
  Susp^-comm-S-l m n {A} =
    Susp^-comm (S m) n {A} ◃∎
      =ₛ₁⟨ ! (Susp^-comm-! n (S m) {A}) ⟩
    ! (Susp^-comm n (S m) {A}) ◃∎
      =ₛ⟨ !-=ₛ (Susp^-comm-S-r n m {A}) ⟩
    ! (ap Susp (Susp^-comm n m)) ◃∙
    ! (Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 0 & 1 & !-ap Susp (Susp^-comm n m) ⟩
    ap Susp (! (Susp^-comm n m)) ◃∙
    ! (Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 0 & 1 & ap (ap Susp) (Susp^-comm-! n m) ⟩
    ap Susp (Susp^-comm m n) ◃∙
    ! (Susp^-comm n 1) ◃∎
      =ₛ₁⟨ 1 & 1 & Susp^-comm-! n 1 ⟩
    ap Susp (Susp^-comm m n) ◃∙
    Susp^-comm 1 n ◃∎ ∎ₛ

  Susp^-comm-S-1 : ∀ {i} (m : ℕ) {A : Type i}
    → Susp^-comm (S m) 1 {A} == ap Susp (Susp^-comm m 1 {A})
  Susp^-comm-S-1 m {A} = =ₛ-out $
    Susp^-comm (S m) 1 {A} ◃∎
      =ₛ⟨ Susp^-comm-S-l m 1 ⟩
    ap Susp (Susp^-comm m 1) ◃∙
    Susp^-comm 1 1 ◃∎
      =ₛ⟨ 1 & 1 & Susp^-comm-diag 1 ⟩
    ap Susp (Susp^-comm m 1) ◃∎ ∎ₛ

  Susp^-comm-1-S : ∀ {i} (n : ℕ) {A : Type i}
    → Susp^-comm 1 (S n) {A} == ap Susp (Susp^-comm 1 n {A})
  Susp^-comm-1-S n {A} =
    Susp^-comm 1 (S n) {A}
      =⟨ ! (Susp^-comm-! (S n) 1 {A}) ⟩
    ! (Susp^-comm (S n) 1 {A})
      =⟨ ap ! (Susp^-comm-S-1 n {A}) ⟩
    ! (ap Susp (Susp^-comm n 1 {A}))
      =⟨ !-ap Susp (Susp^-comm n 1 {A}) ⟩
    ap Susp (! (Susp^-comm n 1 {A}))
      =⟨ ap (ap Susp) (Susp^-comm-! n 1 {A}) ⟩
    ap Susp (Susp^-comm 1 n {A}) =∎

  Susp^-comm-S-S : ∀ {i} (m n : ℕ) {A : Type i}
    → Susp^-comm (S m) (S n) {A} == ap Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n)
  Susp^-comm-S-S m n {A} = =ₛ-out {t = ap Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) ◃∎} $
    Susp^-comm (S m) (S n) {A} ◃∎
      =ₛ⟨ Susp^-comm-S-l m (S n) ⟩
    ap Susp (Susp^-comm m (S n)) ◃∙
    Susp^-comm 1 (S n) ◃∎
      =ₛ₁⟨ 1 & 1 & Susp^-comm-1-S n ⟩
    ap Susp (Susp^-comm m (S n)) ◃∙
    ap Susp (Susp^-comm 1 n) ◃∎
      =ₛ⟨ ∙-ap-seq Susp (Susp^-comm m (S n) ◃∙ Susp^-comm 1 n ◃∎) ⟩
    ap Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) ◃∎ ∎ₛ

Susp^-fmap : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j}
  → (A → B) → Susp^ n A → Susp^ n B
Susp^-fmap O f = f
Susp^-fmap (S n) f = Susp-fmap (Susp^-fmap n f)

⊙Susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Susp^ n X ⊙→ ⊙Susp^ n Y
⊙Susp^-fmap O f = f
⊙Susp^-fmap (S n) f = ⊙Susp-fmap (Susp^-fmap n (fst f))

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
  → ⊙Susp^-fmap n (⊙idf X) == ⊙idf (⊙Susp^ n X)
⊙Susp^-fmap-idf O X = idp
⊙Susp^-fmap-idf (S n) X =
  ap ⊙Susp-fmap (Susp^-fmap-idf n (de⊙ X)) ∙ ⊙Susp-fmap-idf (Susp^ n (de⊙ X))

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

Susp^-fmap-flip : ∀ {i} (m : ℕ) {A : Type i} (s : Susp^ (S m) (Susp A))
  → Susp^-fmap (S m) Susp-flip s == Susp-flip s
Susp^-fmap-flip O {A} s = Susp-fmap-flip s
Susp^-fmap-flip (S m) {A} s =
  Susp^-fmap (S (S m)) Susp-flip s
    =⟨ ap (λ f → Susp-fmap f s) (λ= (Susp^-fmap-flip m)) ⟩
  Susp-fmap Susp-flip s
    =⟨ Susp-fmap-flip s ⟩
  Susp-flip s =∎

Susp^-comm-flip : ∀ {i} (m n : ℕ) (A : Type i)
  → Susp^-fmap n (Susp-flip {A = Susp^ m A}) ∘ coe (Susp^-comm (S m) n) ∼
    coe (Susp^-comm (S m) n) ∘ Susp-flip {A = Susp^ m (Susp^ n A)}
Susp^-comm-flip m O A s =
  Susp-flip (coe (Susp^-comm (S m) 0) s)
    =⟨ ap (λ p → Susp-flip (coe p s)) (Susp^-comm-0-r (S m) A) ⟩
  Susp-flip s
    =⟨ ap (λ p → coe p (Susp-flip s)) (! (Susp^-comm-0-r (S m) A)) ⟩
  coe (Susp^-comm (S m) 0) (Susp-flip s) =∎
Susp^-comm-flip m (S n) A s =
  Susp^-fmap (S n) Susp-flip (coe (Susp^-comm (S m) (S n)) s)
    =⟨ Susp^-fmap-flip n (coe (Susp^-comm (S m) (S n)) s) ⟩
  Susp-flip (coe (Susp^-comm (S m) (S n)) s)
    =⟨ ap (λ p → Susp-flip (coe p s)) (Susp^-comm-S-S m n) ⟩
  Susp-flip (transport Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) s)
    =⟨ ! (ap Susp-flip (Susp-fmap-coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n) s)) ⟩
  Susp-flip (Susp-fmap (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) s)
    =⟨ Susp-flip-natural (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) s ⟩
  Susp-fmap (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) (Susp-flip s)
    =⟨ Susp-fmap-coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n) (Susp-flip s) ⟩
  transport Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) (Susp-flip s)
    =⟨ ! (ap (λ p → coe p (Susp-flip s)) (Susp^-comm-S-S m n)) ⟩
  coe (Susp^-comm (S m) (S n)) (Susp-flip s) =∎

abstract
  maybe-Susp^-flip-Susp^-comm : ∀ {i} (A : Type i) (m n : ℕ) (b : Bool)
    → Susp^-fmap n (maybe-Susp^-flip m b) ∘ coe (Susp^-comm m n {A = A}) ∼
      coe (Susp^-comm m n {A = A}) ∘ maybe-Susp^-flip m b
  maybe-Susp^-flip-Susp^-comm A O n b s =
    Susp^-fmap n (idf A) (coe (Susp^-comm 0 n) s)
      =⟨ ap (λ p → Susp^-fmap n (idf A) (coe p s))
            (Susp^-comm-0-l n _) ⟩
    Susp^-fmap n (idf A) s
      =⟨ app= (Susp^-fmap-idf n A) s ⟩
    s
      =⟨ ap (λ p → coe p s) (! (Susp^-comm-0-l n _)) ⟩
    coe (Susp^-comm 0 n) s =∎
  maybe-Susp^-flip-Susp^-comm A (S m) n true = Susp^-comm-flip m n A
  maybe-Susp^-flip-Susp^-comm A (S m) n false s =
    Susp^-fmap n (idf (Susp (Susp^ m A))) (coe (Susp^-comm (S m) n) s)
      =⟨ app= (Susp^-fmap-idf n _) (coe (Susp^-comm (S m) n) s) ⟩
    coe (Susp^-comm (S m) n) s =∎

abstract
  Susp^-+-natural : ∀ {i j} (m n : ℕ) {A : Type i} {B : Type j} (f : A → B)
    → coe (Susp^-+ m n) ∘ Susp^-fmap m (Susp^-fmap n f) ∼
      Susp^-fmap (m + n) f ∘ coe (Susp^-+ m n)
  Susp^-+-natural O n f sa = idp
  Susp^-+-natural (S m) n f sa =
    transport Susp (Susp^-+ m n) (Susp^-fmap (S m) (Susp^-fmap n f) sa)
      =⟨ ! (Susp-fmap-coe (Susp^-+ m n) (Susp^-fmap (S m) (Susp^-fmap n f) sa)) ⟩
    Susp-fmap (coe (Susp^-+ m n)) (Susp^-fmap (S m) (Susp^-fmap n f) sa)
      =⟨ ! (Susp-fmap-∘ (coe (Susp^-+ m n)) (Susp^-fmap m (Susp^-fmap n f)) sa) ⟩
    Susp-fmap (coe (Susp^-+ m n) ∘ Susp^-fmap m (Susp^-fmap n f)) sa
      =⟨ ap (λ f → Susp-fmap f sa) (λ= (Susp^-+-natural m n f)) ⟩
    Susp-fmap (Susp^-fmap (m + n) f ∘ coe (Susp^-+ m n)) sa
      =⟨ Susp-fmap-∘ (Susp^-fmap (m + n) f) (coe (Susp^-+ m n)) sa ⟩
    Susp^-fmap (S m + n) f (Susp-fmap (coe (Susp^-+ m n)) sa)
      =⟨ ap (Susp^-fmap (S m + n) f) (Susp-fmap-coe (Susp^-+ m n) sa) ⟩
    Susp^-fmap (S m + n) f (transport Susp (Susp^-+ m n) sa) =∎

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

module _ {i} (A : Type i) (m : ℕ₋₂) where

  Susp^-Trunc-swap : ∀ (n : ℕ)
    → Susp^ n (Trunc m A)
    → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
  Susp^-Trunc-swap O = idf _
  Susp^-Trunc-swap (S n) =
    Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) ∘
    Susp-fmap (Susp^-Trunc-swap n)

  Susp^-Trunc-swap-maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → Susp^-Trunc-swap n ∘ maybe-Susp^-flip n b ∼
      Trunc-fmap (maybe-Susp^-flip n b) ∘ Susp^-Trunc-swap n
  Susp^-Trunc-swap-maybe-Susp^-flip O b x = ! (Trunc-fmap-idf x)
  Susp^-Trunc-swap-maybe-Susp^-flip (S n) true x =
    (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Susp^-Trunc-swap n) $
     Susp-flip x)
      =⟨ ap (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m)) $
         ! $ Susp-flip-natural (Susp^-Trunc-swap n) x ⟩
    (Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
     Susp-flip $
     Susp-fmap (Susp^-Trunc-swap n) x)
      =⟨ Susp-Trunc-swap-Susp-flip (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Susp^-Trunc-swap n) x ⟩
    (Trunc-fmap Susp-flip $
     Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Susp^-Trunc-swap n) x) =∎
  Susp^-Trunc-swap-maybe-Susp^-flip (S n) false x = ! (Trunc-fmap-idf (Susp^-Trunc-swap (S n) x))

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

module _ {i} {j} {A : Type i} {B : Type j} (f : A → B) (m : ℕ₋₂) where

  Susp^-Trunc-swap-natural : ∀ (n : ℕ)
    → Susp^-Trunc-swap B m n ∘ Susp^-fmap n (Trunc-fmap f) ∼
      Trunc-fmap (Susp^-fmap n f) ∘ Susp^-Trunc-swap A m n
  Susp^-Trunc-swap-natural O s = idp
  Susp^-Trunc-swap-natural (S n) s =
    (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Susp^-Trunc-swap B m n) $
     Susp^-fmap (S n) (Trunc-fmap f) s)
      =⟨ ap (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m)) $
         ! $ Susp-fmap-∘ (Susp^-Trunc-swap B m n) (Susp^-fmap n (Trunc-fmap f)) s ⟩
    (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Susp^-Trunc-swap B m n ∘ Susp^-fmap n (Trunc-fmap f)) s)
      =⟨ ap (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m)) $
         app= (ap Susp-fmap (λ= (Susp^-Trunc-swap-natural n))) s ⟩
    (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Trunc-fmap (Susp^-fmap n f) ∘ Susp^-Trunc-swap A m n) s)
      =⟨ ap (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m)) $
         Susp-fmap-∘ (Trunc-fmap (Susp^-fmap n f)) (Susp^-Trunc-swap A m n) s ⟩
    (Susp-Trunc-swap (Susp^ n B) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Trunc-fmap (Susp^-fmap n f)) $
     Susp-fmap (Susp^-Trunc-swap A m n) s)
      =⟨ Susp-Trunc-swap-natural (Susp^-fmap n f) (⟨ n ⟩₋₂ +2+ m) $
         Susp-fmap (Susp^-Trunc-swap A m n) s ⟩
    (Trunc-fmap (Susp^-fmap (S n) f) $
     Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) $
     Susp-fmap (Susp^-Trunc-swap A m n) s) =∎

  Susp^-Trunc-equiv-natural : ∀ (n : ℕ)
    → –> (Susp^-Trunc-equiv B m n) ∘ Trunc-fmap (Susp^-fmap n (Trunc-fmap f)) ∼
      Trunc-fmap (Susp^-fmap n f) ∘ –> (Susp^-Trunc-equiv A m n)
  Susp^-Trunc-equiv-natural n =
    Trunc-elim {{λ t → =-preserves-level Trunc-level}}
               (Susp^-Trunc-swap-natural n)

  Susp^-Trunc-equiv-natural' : ∀ (n : ℕ)
    → <– (Susp^-Trunc-equiv B m n) ∘ Trunc-fmap (Susp^-fmap n f) ∼
      Trunc-fmap (Susp^-fmap n (Trunc-fmap f)) ∘ <– (Susp^-Trunc-equiv A m n)
  Susp^-Trunc-equiv-natural' n x =
    (<– (Susp^-Trunc-equiv B m n) $
     Trunc-fmap (Susp^-fmap n f) x)
      =⟨ ap (<– (Susp^-Trunc-equiv B m n)) $
         ap (Trunc-fmap (Susp^-fmap n f)) $
         ! $ <–-inv-r (Susp^-Trunc-equiv A m n) x ⟩
    (<– (Susp^-Trunc-equiv B m n) $
     Trunc-fmap (Susp^-fmap n f) $
     –> (Susp^-Trunc-equiv A m n) $
     <– (Susp^-Trunc-equiv A m n) x)
      =⟨ ap (<– (Susp^-Trunc-equiv B m n)) $
         ! $ Susp^-Trunc-equiv-natural n $
         <– (Susp^-Trunc-equiv A m n) x ⟩
    (<– (Susp^-Trunc-equiv B m n) $
     –> (Susp^-Trunc-equiv B m n) $
     Trunc-fmap (Susp^-fmap n (Trunc-fmap f)) $
     <– (Susp^-Trunc-equiv A m n) x)
      =⟨ <–-inv-l (Susp^-Trunc-equiv B m n) $
         Trunc-fmap (Susp^-fmap n (Trunc-fmap f)) $
         <– (Susp^-Trunc-equiv A m n) x ⟩
    (Trunc-fmap (Susp^-fmap n (Trunc-fmap f)) $
     <– (Susp^-Trunc-equiv A m n) x) =∎

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
