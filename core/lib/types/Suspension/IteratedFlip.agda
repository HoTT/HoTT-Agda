{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.FunctionSeq
open import lib.types.Pointed
open import lib.types.Suspension.Core
open import lib.types.Suspension.Flip
open import lib.types.Suspension.Iterated
open import lib.types.Suspension.IteratedEquivs
open import lib.types.Suspension.IteratedTrunc
open import lib.types.Suspension.Trunc
open import lib.types.TLevel
open import lib.types.Truncation

module lib.types.Suspension.IteratedFlip where

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

module _ {i} (X : Ptd i) (m : ℕ₋₂) where

  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip : ∀ (n : ℕ) (b : Bool)
    → ⊙Susp^-Trunc-swap X m n ◃⊙∘
      ⊙maybe-Susp^-flip n b ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙maybe-Susp^-flip n b) ◃⊙∘
      ⊙Susp^-Trunc-swap X m n ◃⊙idf
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip O b =
    =⊙∘-in (! (⊙λ= ⊙Trunc-fmap-⊙idf))
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip (S n) true =
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙∘
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
           ! $ ⊙Susp-flip-natural (⊙Susp^-Trunc-swap X m n) ⟩
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-flip (⊙Trunc (⟨ n ⟩₋₂ +2+ m) (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙Susp-Trunc-swap-⊙Susp-flip (⟨ n ⟩₋₂ +2+ m) ⟩
    ⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp-Trunc-swap (Susp^ n (de⊙ X)) (⟨ n ⟩₋₂ +2+ m) ◃⊙∘
    ⊙Susp-fmap (Susp^-Trunc-swap (de⊙ X) m n) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙contract ⟩
    ⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ n X)) ◃⊙∘
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙idf ∎⊙∘
  ⊙Susp^-Trunc-swap-⊙maybe-Susp^-flip (S n) false =
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙∘
    ⊙idf _ ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand ⊙idf-seq ⟩
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙idf
      =⊙∘₁⟨ 0 & 0 & ! (⊙λ= ⊙Trunc-fmap-⊙idf) ⟩
    ⊙Trunc-fmap (⊙idf (⊙Susp (de⊙ (⊙Susp^ n X)))) ◃⊙∘
    ⊙Susp^-Trunc-swap X m (S n) ◃⊙idf ∎⊙∘
