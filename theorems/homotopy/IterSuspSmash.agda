{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspSmash
open import homotopy.SuspSmashComm

module homotopy.IterSuspSmash where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ∧ Y → Susp^ n (X ∧ Y)
  Σ^∧-out O = idf _
  Σ^∧-out (S n) = Susp-fmap (Σ^∧-out n) ∘ Σ∧-out (⊙Susp^ n X) Y

  ⊙Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ⊙∧ Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙Σ^∧-out O = ⊙idf _
  ⊙Σ^∧-out (S n) = ⊙Susp-fmap (Σ^∧-out n) ⊙∘ ⊙Σ∧-out (⊙Susp^ n X) Y

  ∧Σ^-out : (n : ℕ) → X ∧ ⊙Susp^ n Y → Susp^ n (X ∧ Y)
  ∧Σ^-out O = idf _
  ∧Σ^-out (S n) = Susp-fmap (∧Σ^-out n) ∘ ∧Σ-out X (⊙Susp^ n Y)

  ⊙∧Σ^-out : (n : ℕ) → X ⊙∧ ⊙Susp^ n Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙∧Σ^-out O = ⊙idf _
  ⊙∧Σ^-out (S n) = ⊙Susp-fmap (∧Σ^-out n) ⊙∘ ⊙∧Σ-out X (⊙Susp^ n Y)

private
  maybe-Susp^-flip : ∀ {i} {A : Type i} (n : ℕ)
    → Bool
    → Susp^ n A → Susp^ n A
  maybe-Susp^-flip 0 _ = idf _
  maybe-Susp^-flip (S _) true  = Susp-flip
  maybe-Susp^-flip (S _) false = idf _

odd-Susp^-flip : ∀ {i} {A : Type i} (n : ℕ) → Susp^ n A → Susp^ n A
odd-Susp^-flip n = maybe-Susp^-flip n (odd n)

private
  maybe-Susp^-flip-fmap : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B)
    (n : ℕ) (b : Bool)
    → Susp^-fmap n f ∘ maybe-Susp^-flip n b ∼
      maybe-Susp^-flip n b ∘ Susp^-fmap n f
  maybe-Susp^-flip-fmap f O b s = idp
  maybe-Susp^-flip-fmap f (S n) true s =
    ! (Susp-flip-fmap-comm (Susp^-fmap n f) s)
  maybe-Susp^-flip-fmap f (S n) false s = idp

  maybe-Susp^-flip-fmap-comm : ∀ {i} (A : Type i) (m n : ℕ) (b : Bool)
    → Susp^-fmap n (maybe-Susp^-flip m b) ∘ coe (Susp^-comm m n {A = A}) ∼
      coe (Susp^-comm m n {A = A}) ∘ maybe-Susp^-flip m b
  maybe-Susp^-flip-fmap-comm A O n b s =
    Susp^-fmap n (idf A) (coe (Susp^-comm 0 n) s)
      =⟨ ap (λ p → Susp^-fmap n (idf A) (coe p s))
            (Susp^-comm-0-l n _) ⟩
    Susp^-fmap n (idf A) s
      =⟨ app= (Susp^-fmap-idf n A) s ⟩
    s
      =⟨ ap (λ p → coe p s) (! (Susp^-comm-0-l n _)) ⟩
    coe (Susp^-comm 0 n) s =∎
  maybe-Susp^-flip-fmap-comm A (S m) n true = Susp^-comm-flip m n A
  maybe-Susp^-flip-fmap-comm A (S m) n false s =
    Susp^-fmap n (idf (Susp (Susp^ m A))) (coe (Susp^-comm (S m) n) s)
      =⟨ app= (Susp^-fmap-idf n _) (coe (Susp^-comm (S m) n) s) ⟩
    coe (Susp^-comm (S m) n) s =∎

odd-Susp^-flip-fmap : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B) (n : ℕ)
  → Susp^-fmap n f ∘ odd-Susp^-flip n ∼
    odd-Susp^-flip n ∘ Susp^-fmap n f
odd-Susp^-flip-fmap f n = maybe-Susp^-flip-fmap f n (odd n)

private
  odd-Susp^-flip-S-helper : ∀ {i} {A : Type i} (n : ℕ) (b : Bool)
    → even n == b
    → odd-Susp^-flip {A = A} (S n) ∼ Susp-flip ∘ Susp-fmap (odd-Susp^-flip n)
  odd-Susp^-flip-S-helper {A = A} 0 _ p sa =
    ap Susp-flip (! (Susp-fmap-idf A sa))
  odd-Susp^-flip-S-helper n@(S _) true p sa =
    odd-Susp^-flip (S n) sa
      =⟨ ap (λ b → maybe-Susp^-flip (S n) (negate (negate b)) sa) p ⟩
    Susp-flip sa
      =⟨ ! (ap Susp-flip (Susp-fmap-idf _ sa)) ⟩
    Susp-flip (Susp-fmap (idf _) sa)
      =⟨ ! (ap (λ b → Susp-flip (Susp-fmap (maybe-Susp^-flip n (negate b)) sa)) p) ⟩
    Susp-flip (Susp-fmap (odd-Susp^-flip n) sa) =∎
  odd-Susp^-flip-S-helper n@(S _) false p sa =
    odd-Susp^-flip (S n) sa
      =⟨ ap (λ b → maybe-Susp^-flip (S n) (negate (negate b)) sa) p ⟩
    sa
      =⟨ ! (Susp-flip-flip sa) ⟩
    Susp-flip (Susp-flip sa)
      =⟨ ap Susp-flip (! (Susp-fmap-flip sa)) ⟩
    Susp-flip (Susp-fmap Susp-flip sa)
      =⟨ ! (ap (λ b → Susp-flip (Susp-fmap (maybe-Susp^-flip n (negate b)) sa)) p) ⟩
    Susp-flip (Susp-fmap (odd-Susp^-flip n) sa) =∎

odd-Susp^-flip-S : ∀ {i} {A : Type i} (n : ℕ)
  → odd-Susp^-flip {A = A} (S n) ∼ Susp-flip ∘ Susp-fmap (odd-Susp^-flip n)
odd-Susp^-flip-S n = odd-Susp^-flip-S-helper n (even n) idp

odd-odd-Susp^-flip : ∀ {i} {A : Type i} (n m : ℕ)
  → Susp^ n (Susp^ m A) → Susp^ n (Susp^ m A)
odd-odd-Susp^-flip {A = A} n m = maybe-Susp^-flip n (and (odd n) (odd m))

odd-odd-Susp^-flip-0-r : ∀ {i} {A : Type i} (n : ℕ) →
  odd-odd-Susp^-flip {A = A} n 0 == idf _
odd-odd-Susp^-flip-0-r O = idp
odd-odd-Susp^-flip-0-r n@(S _) = ap (maybe-Susp^-flip n) (and-false-r (odd n))

private
  odd-odd-Susp^-flip-S-r-helper : ∀ {i} {A : Type i} (m n : ℕ) (b c : Bool)
    → maybe-Susp^-flip {A = A} m (and b (negate c)) ∼
      maybe-Susp^-flip m (and b c) ∘ maybe-Susp^-flip m b
  odd-odd-Susp^-flip-S-r-helper O n b c s = idp
  odd-odd-Susp^-flip-S-r-helper {A = A} m@(S _) n true true s = ! (Susp-flip-flip s)
  odd-odd-Susp^-flip-S-r-helper {A = A} m@(S _) n true false s = idp
  odd-odd-Susp^-flip-S-r-helper {A = A} m@(S _) n false c s = idp

odd-odd-Susp^-flip-S-r : ∀ {i} {A : Type i} (m n : ℕ)
  → odd-odd-Susp^-flip {A = A} m (S n) ∼
    maybe-Susp^-flip m (and (odd m) (odd n)) ∘ odd-Susp^-flip m
odd-odd-Susp^-flip-S-r m n =
  odd-odd-Susp^-flip-S-r-helper m n (odd m) (odd n)

∧Σ-Σ^∧-out : ∀ {i} {j} (X : Ptd i) (Y : Ptd j) (m : ℕ) →
    Susp-fmap (∧Σ^-out X Y m) ∘ Σ∧-out X (⊙Susp^ m Y)
  ∼ coe (Susp^-comm m 1) ∘ odd-Susp^-flip m ∘ Susp^-fmap m (Σ∧-out X Y) ∘ ∧Σ^-out (⊙Susp (de⊙ X)) Y m
∧Σ-Σ^∧-out X Y O s =
  Susp-fmap (idf (X ∧ Y)) (Σ∧-out X Y s)
    =⟨ Susp-fmap-idf (X ∧ Y) (Σ∧-out X Y s) ⟩
  Σ∧-out X Y s
    =⟨ ! $ ap (λ p → coe p (Σ∧-out X Y s)) $
       Susp^-comm-0-l 1 (X ∧ Y) ⟩
  coe (Susp^-comm 0 1) (Σ∧-out X Y s) =∎
∧Σ-Σ^∧-out X Y (S m) s =
  Susp-fmap (∧Σ^-out X Y (S m)) (Σ∧-out X (⊙Susp^ (S m) Y) s)
    =⟨ Susp-fmap-∘ (Susp-fmap (∧Σ^-out X Y m))
                   (∧Σ-out X (⊙Susp^ m Y))
                   (Σ∧-out X (⊙Susp^ (S m) Y) s) ⟩
  Susp^-fmap 2 (∧Σ^-out X Y m) (Susp-fmap (∧Σ-out X (⊙Susp^ m Y)) (Σ∧-out X (⊙Susp^ (S m) Y) s))
    =⟨ ap (Susp^-fmap 2 (∧Σ^-out X Y m)) (∧Σ-Σ∧-out X (⊙Susp^ m Y) s) ⟩
  Susp^-fmap 2 (∧Σ^-out X Y m) (Susp-flip
    (Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)))
    =⟨ ! $ Susp-flip-fmap-comm
         (Susp-fmap (∧Σ^-out X Y m))
         (Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)) ⟩
  Susp-flip (Susp^-fmap 2 (∧Σ^-out X Y m) (Susp-fmap (Σ∧-out X (⊙Susp^ m Y))
    (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)))
    =⟨ ! $ ap Susp-flip $
       Susp-fmap-∘
         (Susp-fmap (∧Σ^-out X Y m))
         (Σ∧-out X (⊙Susp^ m Y))
         (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s) ⟩
  Susp-flip (Susp-fmap (Susp-fmap (∧Σ^-out X Y m) ∘ Σ∧-out X (⊙Susp^ m Y))
    (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s))
    =⟨ ap (λ f → Susp-flip (Susp-fmap f (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s))) $
       λ= $ ∧Σ-Σ^∧-out X Y m ⟩
  Susp-flip (Susp-fmap
    (coe (Susp^-comm m 1) ∘
     odd-Susp^-flip m ∘
     Susp^-fmap m (Σ∧-out X Y) ∘
     ∧Σ^-out (⊙Susp (de⊙ X)) Y m)
    (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s))
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1) ∘
          odd-Susp^-flip m ∘
          Susp^-fmap m (Σ∧-out X Y))
         (∧Σ^-out (⊙Susp (de⊙ X)) Y m)
         (∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s) ⟩
  Susp-flip (Susp-fmap
    (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m ∘ Susp^-fmap m (Σ∧-out X Y))
    (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m)
         (Susp^-fmap m (Σ∧-out X Y))
         (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s) ⟩
  Susp-flip (Susp-fmap
    (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)))
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1))
         (odd-Susp^-flip m)
         (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)) ⟩
  Susp-flip (Susp-fmap (coe (Susp^-comm m 1)) (Susp-fmap (odd-Susp^-flip m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))))
    =⟨ Susp-flip-fmap-comm
         (coe (Susp^-comm m 1))
         (Susp-fmap (odd-Susp^-flip m)
           (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))) ⟩
  Susp-fmap (coe (Susp^-comm m 1)) (Susp-flip (Susp-fmap (odd-Susp^-flip m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))))
    =⟨ Susp-fmap-coe
         (Susp^-comm m 1)
         (Susp-flip (Susp-fmap (odd-Susp^-flip m)
           (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)))) ⟩
  transport Susp (Susp^-comm m 1) (Susp-flip (Susp-fmap (odd-Susp^-flip m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))))
    =⟨ ap (λ p → coe p (Susp-flip (Susp-fmap (odd-Susp^-flip m)
                   (Susp^-fmap (S m) (Σ∧-out X Y)
                     (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))))) $
       ! $ Susp^-comm-S-1 m ⟩
  coe (Susp^-comm (S m) 1) (Susp-flip (Susp-fmap (odd-Susp^-flip m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))))
    =⟨ ap (coe (Susp^-comm (S m) 1)) $ ! $
       odd-Susp^-flip-S m
         (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)) ⟩
  coe (Susp^-comm (S m) 1) (odd-Susp^-flip (S m)
    (Susp^-fmap (S m) (Σ∧-out X Y) (∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s))) =∎

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ∧Σ^-Σ^∧-out : ∀ (n m : ℕ) →
      Susp^-fmap n (∧Σ^-out X Y m) ∘ Σ^∧-out X (⊙Susp^ m Y) n
    ∼ coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n) ∘ ∧Σ^-out (⊙Susp^ n X) Y m
  ∧Σ^-Σ^∧-out O m s =
    ∧Σ^-out X Y m s
      =⟨ ! (app= (Susp^-fmap-idf m (X ∧ Y)) (∧Σ^-out X Y m s)) ⟩
    Susp^-fmap m (idf (X ∧ Y)) (∧Σ^-out X Y m s)
      =⟨ app= (! (odd-odd-Susp^-flip-0-r m))
              (Susp^-fmap m (idf (X ∧ Y)) (∧Σ^-out X Y m s)) ⟩
    odd-odd-Susp^-flip m 0 (Susp^-fmap m (idf (X ∧ Y)) (∧Σ^-out X Y m s))
      =⟨ ap (λ p → coe p (odd-odd-Susp^-flip m 0 (Susp^-fmap m (idf (X ∧ Y)) (∧Σ^-out X Y m s))))
            (! (Susp^-comm-0-r m _)) ⟩
    coe (Susp^-comm m 0) (odd-odd-Susp^-flip m 0 (Susp^-fmap m (idf (X ∧ Y)) (∧Σ^-out X Y m s))) =∎
  ∧Σ^-Σ^∧-out (S n) m s =
    Susp^-fmap (S n) (∧Σ^-out X Y m)
      (Susp-fmap (Σ^∧-out X (⊙Susp^ m Y) n) (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s))
      =⟨ ! $ Susp-fmap-∘
           (Susp^-fmap n (∧Σ^-out X Y m))
           (Σ^∧-out X (⊙Susp^ m Y) n)
           (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s) ⟩
    Susp-fmap (Susp^-fmap n (∧Σ^-out X Y m) ∘ Σ^∧-out X (⊙Susp^ m Y) n)
              (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ ap (λ f → Susp-fmap f (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s))
            (λ= (∧Σ^-Σ^∧-out n m)) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n) ∘ ∧Σ^-out (⊙Susp^ n X) Y m)
      (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ Susp-fmap-∘
          (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n))
          (∧Σ^-out (⊙Susp^ n X) Y m)
          (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n))
      (Susp-fmap (∧Σ^-out (⊙Susp^ n X) Y m) (Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s))
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n)))
            (∧Σ-Σ^∧-out (⊙Susp^ n X) Y m s) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n))
      (coe (Susp^-comm m 1) (odd-Susp^-flip m
        (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))))
      =⟨ Susp-fmap-∘
           (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)
           (Susp^-fmap m (Σ^∧-out X Y n))
           (coe (Susp^-comm m 1) (odd-Susp^-flip m
             (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)
      (Susp^-fmap (S m) (Σ^∧-out X Y n)
        (coe (Susp^-comm m 1) (odd-Susp^-flip m
          (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ ! $ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)) $
         Susp^-comm-fmap m 1 (Σ^∧-out X Y n)
           (odd-Susp^-flip m (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)
      (coe (Susp^-comm m 1) (Susp^-fmap m (Susp-fmap (Σ^∧-out X Y n))
        (odd-Susp^-flip m (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) ∘ coe (Susp^-comm m 1)) $
         odd-Susp^-flip-fmap (Susp-fmap (Σ^∧-out X Y n)) m $
         Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s) ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) (coe (Susp^-comm m 1)
      (odd-Susp^-flip m (Susp^-fmap m (Susp-fmap (Σ^∧-out X Y n))
        (Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) ∘ coe (Susp^-comm m 1) ∘ odd-Susp^-flip m) $
         ! $ app= (Susp^-fmap-∘ m (Susp-fmap (Σ^∧-out X Y n)) (Σ∧-out (⊙Susp^ n X) Y)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) (coe (Susp^-comm m 1)
      (odd-Susp^-flip m (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))))
      =⟨ Susp-fmap-∘
           (coe (Susp^-comm m n))
           (odd-odd-Susp^-flip m n)
           (coe (Susp^-comm m 1) (odd-Susp^-flip m
             (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))) ⟩
    Susp-fmap (coe (Susp^-comm m n)) (Susp-fmap (odd-odd-Susp^-flip m n) (coe (Susp^-comm m 1)
      (odd-Susp^-flip m (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n))) $
         maybe-Susp^-flip-fmap-comm _ m 1 (and (odd m) (odd n)) $
         odd-Susp^-flip m (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)) ⟩
    Susp-fmap (coe (Susp^-comm m n)) (coe (Susp^-comm m 1)
      (maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
        (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ Susp-fmap-coe (Susp^-comm m n) $
         coe (Susp^-comm m 1) (maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
           (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))) ⟩
    transport Susp (Susp^-comm m n) (coe (Susp^-comm m 1)
      (maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
        (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))))
      =⟨ ! $ coe-∙ (Susp^-comm m 1) (ap Susp (Susp^-comm m n)) $
         maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
           (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))) ⟩
    coe (Susp^-comm m 1 ∙ ap Susp (Susp^-comm m n))
      (maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
        (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))))
      =⟨ app= (ap coe (! (=ₛ-out (Susp^-comm-S-r m n)))) $
         maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
           (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)))
      ⟩
    coe (Susp^-comm m (S n))
      (maybe-Susp^-flip m (and (odd m) (odd n)) (odd-Susp^-flip m
        (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))))
      =⟨ ! $ ap (coe (Susp^-comm m (S n))) $
         odd-odd-Susp^-flip-S-r m n $
         Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s) ⟩
    coe (Susp^-comm m (S n)) (odd-odd-Susp^-flip m (S n)
      (Susp^-fmap m (Σ^∧-out X Y (S n)) (∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s))) =∎

  ⊙Σ^∧Σ^-out : ∀ (n m : ℕ) → ⊙Susp^ n X ⊙∧ ⊙Susp^ m Y ⊙→ ⊙Susp^ (n + m) (X ⊙∧ Y)
  ⊙Σ^∧Σ^-out n m =
    ⊙coe (⊙Susp^-+ n m {X ⊙∧ Y}) ⊙∘
    ⊙Susp^-fmap n (⊙∧Σ^-out X Y m) ⊙∘
    ⊙Σ^∧-out X (⊙Susp^ m Y) n

  Σ^∧Σ^-out : ∀ (n m : ℕ) → ⊙Susp^ n X ∧ ⊙Susp^ m Y → Susp^ (n + m) (X ∧ Y)
  Σ^∧Σ^-out n m = fst (⊙Σ^∧Σ^-out n m)
