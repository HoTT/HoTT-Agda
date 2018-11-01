{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspSmash
open import homotopy.SuspSmashComm

module homotopy.IterSuspSmash where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ∧ Y → Susp^ n (X ∧ Y)
  Σ^∧-out O = idf _
  Σ^∧-out (S n) = Susp-fmap (Σ^∧-out n) ∘ Σ∧-out (⊙Susp^ n X) Y

  private
    Σ^∧-out-pt : (n : ℕ) → Σ^∧-out n (pt (⊙Susp^ n X ⊙∧ Y)) == pt (⊙Susp^ n (X ⊙∧ Y))
    Σ^∧-out-pt O = idp
    Σ^∧-out-pt (S n) = idp

  ⊙Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ⊙∧ Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙Σ^∧-out n = Σ^∧-out n , Σ^∧-out-pt n

  ∧Σ^-out : (n : ℕ) → X ∧ ⊙Susp^ n Y → Susp^ n (X ∧ Y)
  ∧Σ^-out O = idf _
  ∧Σ^-out (S n) = Susp-fmap (∧Σ^-out n) ∘ ∧Σ-out X (⊙Susp^ n Y)

  private
    ∧Σ^-out-pt : (n : ℕ) → ∧Σ^-out n (pt (X ⊙∧ ⊙Susp^ n Y)) == pt (⊙Susp^ n (X ⊙∧ Y))
    ∧Σ^-out-pt O = idp
    ∧Σ^-out-pt (S n) = idp

  ⊙∧Σ^-out : (n : ℕ) → X ⊙∧ ⊙Susp^ n Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙∧Σ^-out n = ∧Σ^-out n , ∧Σ^-out-pt n

private
  maybe-Susp^-flip-+ : ∀ {i} {A : Type i} (m n : ℕ)
    (b : Bool)
    → (m == 0 → b == false)
    → coe (Susp^-+ m n {A}) ∘ maybe-Susp^-flip {A = Susp^ n A} m b ∼
      maybe-Susp^-flip (m + n) b ∘ coe (Susp^-+ m n)
  maybe-Susp^-flip-+ O O b h s = idp
  maybe-Susp^-flip-+ O (S n) true h s = ⊥-elim (Bool-true≠false (h idp))
  maybe-Susp^-flip-+ O (S n) false h s = idp
  maybe-Susp^-flip-+ (S m) n true h s =
    transport Susp (Susp^-+ m n) (Susp-flip s)
      =⟨ ! (Susp-fmap-coe (Susp^-+ m n) (Susp-flip s)) ⟩
    Susp-fmap (coe (Susp^-+ m n)) (Susp-flip s)
      =⟨ ! (Susp-flip-natural (coe (Susp^-+ m n)) s) ⟩
    Susp-flip (Susp-fmap (coe (Susp^-+ m n)) s)
      =⟨ ap Susp-flip (Susp-fmap-coe (Susp^-+ m n) s) ⟩
    Susp-flip (transport Susp (Susp^-+ m n) s) =∎
  maybe-Susp^-flip-+ (S m) n false h s = idp

  maybe-Susp^-flip-comm : ∀ {i} {A : Type i} (m n : ℕ)
    (b : Bool)
    → (m == 0 → b == false)
    → (n == 0 → b == false)
    → coe (Susp^-comm m n {A}) ∘ maybe-Susp^-flip {A = Susp^ n A} m b ∼
      maybe-Susp^-flip {A = Susp^ m A} n b ∘ coe (Susp^-comm m n)
  maybe-Susp^-flip-comm O O b h₁ h₂ s = idp
  maybe-Susp^-flip-comm O (S _) true h₁ h₂ s = ⊥-elim (Bool-true≠false (h₁ idp))
  maybe-Susp^-flip-comm O (S _) false h₁ h₂ s = idp
  maybe-Susp^-flip-comm (S m) O true h₁ h₂ s = ⊥-elim (Bool-true≠false (h₂ idp))
  maybe-Susp^-flip-comm (S m) O false h₁ h₂ s = idp
  maybe-Susp^-flip-comm (S m) (S n) true h₁ h₂ s =
    coe (Susp^-comm (S m) (S n)) (Susp-flip s)
      =⟨ app= (ap coe (Susp^-comm-S-S m n)) (Susp-flip s) ⟩
    transport Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) (Susp-flip s)
      =⟨ ! (Susp-fmap-coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n) (Susp-flip s)) ⟩
    Susp-fmap (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) (Susp-flip s)
      =⟨ ! (Susp-flip-natural (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) s) ⟩
    Susp-flip (Susp-fmap (coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) s)
      =⟨ ap Susp-flip (Susp-fmap-coe (Susp^-comm m (S n) ∙ Susp^-comm 1 n) s) ⟩
    Susp-flip (transport Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) s)
      =⟨ ap Susp-flip (app= (ap coe (! (Susp^-comm-S-S m n))) s) ⟩
    Susp-flip (coe (Susp^-comm (S m) (S n)) s) =∎
  maybe-Susp^-flip-comm (S m) (S n) false h₁ h₂ s = idp

  maybe-Susp^-flip-inv : ∀ {i} {A : Type i} (m : ℕ) (b : Bool)
    → maybe-Susp^-flip m b ∘ maybe-Susp^-flip m b ∼
      idf (Susp^ m A)
  maybe-Susp^-flip-inv O b s = idp
  maybe-Susp^-flip-inv m@(S _) true s = Susp-flip-flip s
  maybe-Susp^-flip-inv m@(S _) false s = idp

abstract
  maybe-Susp^-flip-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B)
    (n : ℕ) (b : Bool)
    → Susp^-fmap n f ∘ maybe-Susp^-flip n b ∼
      maybe-Susp^-flip n b ∘ Susp^-fmap n f
  maybe-Susp^-flip-natural f O b s = idp
  maybe-Susp^-flip-natural f (S n) true s =
    ! (Susp-flip-natural (Susp^-fmap n f) s)
  maybe-Susp^-flip-natural f (S n) false s = idp

odd-Susp^-flip : ∀ {i} {A : Type i} (n : ℕ) → Susp^ n A → Susp^ n A
odd-Susp^-flip n = maybe-Susp^-flip n (odd n)

odd-Susp^-flip-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B) (n : ℕ)
  → Susp^-fmap n f ∘ odd-Susp^-flip n ∼
    odd-Susp^-flip n ∘ Susp^-fmap n f
odd-Susp^-flip-natural f n = maybe-Susp^-flip-natural f n (odd n)

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

odd-odd-Susp^-flip-comm : ∀ {i} {A : Type i} (m n : ℕ)
  → odd-odd-Susp^-flip n m ∘ coe (Susp^-comm m n {A}) ∼
    coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n
odd-odd-Susp^-flip-comm {A = A} m n s =
  odd-odd-Susp^-flip n m (coe (Susp^-comm m n {A}) s)
    =⟨ ! $ maybe-Susp^-flip-comm m n (and (odd n) (odd m))
         (λ p → ap (λ k → and (odd n) (odd k)) p ∙ and-false-r (odd n))
         (ap (λ k → and (odd k) (odd m)))
         s ⟩
  coe (Susp^-comm m n) (maybe-Susp^-flip m (and (odd n) (odd m)) s)
    =⟨ ap (coe (Susp^-comm m n)) $
       app= (ap (maybe-Susp^-flip m) (and-comm (odd n) (odd m))) s ⟩
  coe (Susp^-comm m n) (odd-odd-Susp^-flip m n s) =∎

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
  (Susp-fmap (idf (X ∧ Y)) $
   Σ∧-out X Y s)
    =⟨ Susp-fmap-idf (X ∧ Y) (Σ∧-out X Y s) ⟩
  Σ∧-out X Y s
    =⟨ ! $ ap (λ p → coe p (Σ∧-out X Y s)) $
       Susp^-comm-0-l 1 (X ∧ Y) ⟩
  (coe (Susp^-comm 0 1) $
   Σ∧-out X Y s) =∎
∧Σ-Σ^∧-out X Y (S m) s =
  (Susp-fmap (∧Σ^-out X Y (S m)) $
   Σ∧-out X (⊙Susp^ (S m) Y) s)
    =⟨ Susp-fmap-∘ (Susp-fmap (∧Σ^-out X Y m)) (∧Σ-out X (⊙Susp^ m Y)) $
       Σ∧-out X (⊙Susp^ (S m) Y) s ⟩
  (Susp^-fmap 2 (∧Σ^-out X Y m) $
   Susp-fmap (∧Σ-out X (⊙Susp^ m Y)) $
   Σ∧-out X (⊙Susp^ (S m) Y) s)
    =⟨ ap (Susp^-fmap 2 (∧Σ^-out X Y m)) (∧Σ-Σ∧-out X (⊙Susp^ m Y) s) ⟩
  (Susp^-fmap 2 (∧Σ^-out X Y m) $
   Susp-flip $
   Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) $
   ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)
    =⟨ ! $ Susp-flip-natural (Susp-fmap (∧Σ^-out X Y m)) $
       Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) $
       ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s ⟩
  (Susp-flip $
   Susp^-fmap 2 (∧Σ^-out X Y m) $
   Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) $
   ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)
    =⟨ ap Susp-flip $
       ! $ Susp-fmap-∘ (Susp-fmap (∧Σ^-out X Y m)) (Σ∧-out X (⊙Susp^ m Y)) $
       ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s ⟩
  (Susp-flip $
   Susp-fmap (Susp-fmap (∧Σ^-out X Y m) ∘ Σ∧-out X (⊙Susp^ m Y)) $
   ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)
    =⟨ ap Susp-flip $
       app= (ap Susp-fmap (λ= (∧Σ-Σ^∧-out X Y m))) $
       ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s ⟩
  (Susp-flip $
   Susp-fmap
    (coe (Susp^-comm m 1) ∘
     odd-Susp^-flip m ∘
     Susp^-fmap m (Σ∧-out X Y) ∘
     ∧Σ^-out (⊙Susp (de⊙ X)) Y m) $
   ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s)
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1) ∘
          odd-Susp^-flip m ∘
          Susp^-fmap m (Σ∧-out X Y))
         (∧Σ^-out (⊙Susp (de⊙ X)) Y m) $
       ∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) s ⟩
  (Susp-flip $
   Susp-fmap (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m ∘ Susp^-fmap m (Σ∧-out X Y)) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m)
         (Susp^-fmap m (Σ∧-out X Y)) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (Susp-flip $
   Susp-fmap (coe (Susp^-comm m 1) ∘ odd-Susp^-flip m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ ap Susp-flip $
       Susp-fmap-∘
         (coe (Susp^-comm m 1))
         (odd-Susp^-flip m) $
       Susp^-fmap (S m) (Σ∧-out X Y) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (Susp-flip $
   Susp-fmap (coe (Susp^-comm m 1)) $
   Susp-fmap (odd-Susp^-flip m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ Susp-flip-natural (coe (Susp^-comm m 1)) $
       Susp-fmap (odd-Susp^-flip m) $
       Susp^-fmap (S m) (Σ∧-out X Y) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (Susp-fmap (coe (Susp^-comm m 1)) $
   Susp-flip $
   Susp-fmap (odd-Susp^-flip m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ Susp-fmap-coe (Susp^-comm m 1) $
       Susp-flip $
       Susp-fmap (odd-Susp^-flip m) $
       Susp^-fmap (S m) (Σ∧-out X Y) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (transport Susp (Susp^-comm m 1) $
   Susp-flip $
   Susp-fmap (odd-Susp^-flip m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ app= (ap coe (! (Susp^-comm-S-1 m))) $
       Susp-flip $
       Susp-fmap (odd-Susp^-flip m) $
       Susp^-fmap (S m) (Σ∧-out X Y) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (coe (Susp^-comm (S m) 1) $
   Susp-flip $
   Susp-fmap (odd-Susp^-flip m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s)
    =⟨ ap (coe (Susp^-comm (S m) 1)) $
       ! $ odd-Susp^-flip-S m $
       Susp^-fmap (S m) (Σ∧-out X Y) $
       ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s ⟩
  (coe (Susp^-comm (S m) 1) $
   odd-Susp^-flip (S m) $
   Susp^-fmap (S m) (Σ∧-out X Y) $
   ∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) s) =∎

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ∧Σ^-Σ^∧-out : ∀ (n m : ℕ)
    → Susp^-fmap n (∧Σ^-out X Y m) ∘ Σ^∧-out X (⊙Susp^ m Y) n
    ∼ coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n) ∘ ∧Σ^-out (⊙Susp^ n X) Y m
  ∧Σ^-Σ^∧-out O m s =
    ∧Σ^-out X Y m s
      =⟨ ! (app= (Susp^-fmap-idf m (X ∧ Y)) (∧Σ^-out X Y m s)) ⟩
    (Susp^-fmap m (idf (X ∧ Y)) $
     ∧Σ^-out X Y m s)
      =⟨ app= (! (odd-odd-Susp^-flip-0-r m)) $
         Susp^-fmap m (idf (X ∧ Y)) $
         ∧Σ^-out X Y m s ⟩
    (odd-odd-Susp^-flip m 0 $
     Susp^-fmap m (idf (X ∧ Y)) $
     ∧Σ^-out X Y m s)
      =⟨ app= (ap (λ p → coe p) (! (Susp^-comm-0-r m _))) $
         odd-odd-Susp^-flip m 0 $
         Susp^-fmap m (idf (X ∧ Y)) $
         ∧Σ^-out X Y m s ⟩
    (coe (Susp^-comm m 0) $
     odd-odd-Susp^-flip m 0 $
     Susp^-fmap m (idf (X ∧ Y)) $
     ∧Σ^-out X Y m s) =∎
  ∧Σ^-Σ^∧-out (S n) m s =
    (Susp^-fmap (S n) (∧Σ^-out X Y m) $
     Susp-fmap (Σ^∧-out X (⊙Susp^ m Y) n) $
     Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ ! $ Susp-fmap-∘ (Susp^-fmap n (∧Σ^-out X Y m)) (Σ^∧-out X (⊙Susp^ m Y) n) $
         Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s ⟩
    (Susp-fmap (Susp^-fmap n (∧Σ^-out X Y m) ∘ Σ^∧-out X (⊙Susp^ m Y) n) $
     Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ app= (ap Susp-fmap (λ= (∧Σ^-Σ^∧-out n m))) $
         Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘
                odd-odd-Susp^-flip m n ∘
                Susp^-fmap m (Σ^∧-out X Y n) ∘
                ∧Σ^-out (⊙Susp^ n X) Y m) $
     Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ Susp-fmap-∘
          (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n))
          (∧Σ^-out (⊙Susp^ n X) Y m) $
         Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n)) $
     Susp-fmap (∧Σ^-out (⊙Susp^ n X) Y m) $
     Σ∧-out (⊙Susp^ n X) (⊙Susp^ m Y) s)
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n))) $
         ∧Σ-Σ^∧-out (⊙Susp^ n X) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (Σ^∧-out X Y n)) $
     coe (Susp^-comm m 1) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ Susp-fmap-∘
           (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)
           (Susp^-fmap m (Σ^∧-out X Y n)) $
         coe (Susp^-comm m 1) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) $
     Susp^-fmap (S m) (Σ^∧-out X Y n) $
     coe (Susp^-comm m 1) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)) $
         ! $ Susp^-comm-natural m 1 (Σ^∧-out X Y n) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) $
     coe (Susp^-comm m 1) $
     Susp^-fmap m (Susp-fmap (Σ^∧-out X Y n)) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)) $
         ap (coe (Susp^-comm m 1)) $
         odd-Susp^-flip-natural (Susp-fmap (Σ^∧-out X Y n)) m $
         Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) $
     coe (Susp^-comm m 1) $
     odd-Susp^-flip m $
     Susp^-fmap m (Susp-fmap (Σ^∧-out X Y n)) $
     Susp^-fmap m (Σ∧-out (⊙Susp^ n X) Y) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n)) $
         ap (coe (Susp^-comm m 1)) $
         ap (odd-Susp^-flip m) $
         ! $ app= (Susp^-fmap-∘ m (Susp-fmap (Σ^∧-out X Y n)) (Σ∧-out (⊙Susp^ n X) Y)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n) $
     coe (Susp^-comm m 1) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ Susp-fmap-∘ (coe (Susp^-comm m n)) (odd-odd-Susp^-flip m n) $
         coe (Susp^-comm m 1) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n)) $
     Susp-fmap (odd-odd-Susp^-flip m n) $
     coe (Susp^-comm m 1) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ap (Susp-fmap (coe (Susp^-comm m n))) $
         maybe-Susp^-flip-Susp^-comm _ m 1 (and (odd m) (odd n)) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (Susp-fmap (coe (Susp^-comm m n)) $
     coe (Susp^-comm m 1) $
     maybe-Susp^-flip m (and (odd m) (odd n)) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ Susp-fmap-coe (Susp^-comm m n) $
         coe (Susp^-comm m 1) $
         maybe-Susp^-flip m (and (odd m) (odd n)) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (transport Susp (Susp^-comm m n) $
     coe (Susp^-comm m 1) $
     maybe-Susp^-flip m (and (odd m) (odd n)) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ! $ coe-∙ (Susp^-comm m 1) (ap Susp (Susp^-comm m n)) $
         maybe-Susp^-flip m (and (odd m) (odd n)) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (coe (Susp^-comm m 1 ∙ ap Susp (Susp^-comm m n)) $
     maybe-Susp^-flip m (and (odd m) (odd n)) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ app= (ap coe (! (=ₛ-out (Susp^-comm-S-r m n)))) $
         maybe-Susp^-flip m (and (odd m) (odd n)) $
         odd-Susp^-flip m $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s
       ⟩
    (coe (Susp^-comm m (S n)) $
     maybe-Susp^-flip m (and (odd m) (odd n)) $
     odd-Susp^-flip m $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s)
      =⟨ ! $ ap (coe (Susp^-comm m (S n))) $
         odd-odd-Susp^-flip-S-r m n $
         Susp^-fmap m (Σ^∧-out X Y (S n)) $
         ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s ⟩
    (coe (Susp^-comm m (S n)) $
     odd-odd-Susp^-flip m (S n) $
     Susp^-fmap m (Σ^∧-out X Y (S n)) $
     ∧Σ^-out (⊙Susp (Susp^ n (de⊙ X))) Y m s) =∎

  ∧Σ^-Σ^∧-out' : ∀ (m n : ℕ)
    → Susp^-fmap n (Σ^∧-out X Y m) ∘ ∧Σ^-out (⊙Susp^ m X) Y n
    ∼ coe (Susp^-comm m n) ∘ odd-odd-Susp^-flip m n ∘ Susp^-fmap m (∧Σ^-out X Y n) ∘ Σ^∧-out X (⊙Susp^ n Y) m
  ∧Σ^-Σ^∧-out' m n s =
    (Susp^-fmap n (Σ^∧-out X Y m) $
     ∧Σ^-out (⊙Susp^ m X) Y n s)
      =⟨ ! $ maybe-Susp^-flip-inv n (and (odd n) (odd m)) $
         Susp^-fmap n (Σ^∧-out X Y m) $
         ∧Σ^-out (⊙Susp^ m X) Y n s ⟩
    (odd-odd-Susp^-flip n m $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (Σ^∧-out X Y m) $
     ∧Σ^-out (⊙Susp^ m X) Y n s)
      =⟨ ap (odd-odd-Susp^-flip n m) $
         app= (ap coe (! (!-inv-r (Susp^-comm n m)))) $
         odd-odd-Susp^-flip n m $
         Susp^-fmap n (Σ^∧-out X Y m) $
         ∧Σ^-out (⊙Susp^ m X) Y n s ⟩
    (odd-odd-Susp^-flip n m $
     coe (Susp^-comm n m ∙ ! (Susp^-comm n m)) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (Σ^∧-out X Y m) $
     ∧Σ^-out (⊙Susp^ m X) Y n s)
      =⟨ ap (odd-odd-Susp^-flip n m) $
         coe-∙ (Susp^-comm n m) (! (Susp^-comm n m)) $
         odd-odd-Susp^-flip n m $
         Susp^-fmap n (Σ^∧-out X Y m) $
         ∧Σ^-out (⊙Susp^ m X) Y n s ⟩
    (odd-odd-Susp^-flip n m $
     coe (! (Susp^-comm n m)) $
     coe (Susp^-comm n m) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (Σ^∧-out X Y m) $
     ∧Σ^-out (⊙Susp^ m X) Y n s)
      =⟨ ap (odd-odd-Susp^-flip n m) $
         ap (coe (! (Susp^-comm n m))) $
         ! $ ∧Σ^-Σ^∧-out m n s ⟩
    (odd-odd-Susp^-flip n m $
     coe (! (Susp^-comm n m)) $
     Susp^-fmap m (∧Σ^-out X Y n) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ ap (odd-odd-Susp^-flip n m) $
         app= (ap coe (Susp^-comm-! n m)) $
         Susp^-fmap m (∧Σ^-out X Y n) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (odd-odd-Susp^-flip n m $
     coe (Susp^-comm m n) $
     Susp^-fmap m (∧Σ^-out X Y n) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ odd-odd-Susp^-flip-comm m n $
         Susp^-fmap m (∧Σ^-out X Y n) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (coe (Susp^-comm m n) $
     odd-odd-Susp^-flip m n $
     Susp^-fmap m (∧Σ^-out X Y n) $
     Σ^∧-out X (⊙Susp^ n Y) m s) =∎

  ⊙Σ^∧Σ^-out : ∀ (m n : ℕ) → ⊙Susp^ m X ⊙∧ ⊙Susp^ n Y ⊙→ ⊙Susp^ (m + n) (X ⊙∧ Y)
  ⊙Σ^∧Σ^-out m n =
    ⊙coe' (Susp^-+ m n {X ∧ Y}) (Susp^-+-pt m n {X ⊙∧ Y}) ⊙∘
    ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) m

  Σ^∧Σ^-out : ∀ (m n : ℕ) → ⊙Susp^ m X ∧ ⊙Susp^ n Y → Susp^ (m + n) (X ∧ Y)
  Σ^∧Σ^-out m n =
    coe (Susp^-+ m n {X ∧ Y}) ∘
    Susp^-fmap m (∧Σ^-out X Y n) ∘
    Σ^∧-out X (⊙Susp^ n Y) m

  swap-Σ^∧-out : ∀ (m : ℕ)
    → Susp^-fmap m (∧-swap X Y) ∘ Σ^∧-out X Y m ∼
      ∧Σ^-out Y X m ∘ ∧-swap (⊙Susp^ m X) Y
  swap-Σ^∧-out O s = idp
  swap-Σ^∧-out (S m) s =
    Susp^-fmap (S m) (∧-swap X Y) (Susp-fmap (Σ^∧-out X Y m) (Σ∧-out (⊙Susp^ m X) Y s))
      =⟨ ! (Susp-fmap-∘ (Susp^-fmap m (∧-swap X Y)) (Σ^∧-out X Y m) (Σ∧-out (⊙Susp^ m X) Y s)) ⟩
    Susp-fmap (Susp^-fmap m (∧-swap X Y) ∘ Σ^∧-out X Y m) (Σ∧-out (⊙Susp^ m X) Y s)
      =⟨ ap (λ f → Susp-fmap f (Σ∧-out (⊙Susp^ m X) Y s)) (λ= (swap-Σ^∧-out m)) ⟩
    Susp-fmap (∧Σ^-out Y X m ∘ ∧-swap (⊙Susp^ m X) Y) (Σ∧-out (⊙Susp^ m X) Y s)
      =⟨ Susp-fmap-∘ (∧Σ^-out Y X m) (∧-swap (⊙Susp^ m X) Y) (Σ∧-out (⊙Susp^ m X) Y s) ⟩
    Susp-fmap (∧Σ^-out Y X m) (Susp-fmap (∧-swap (⊙Susp^ m X) Y) (Σ∧-out (⊙Susp^ m X) Y s))
      =⟨ ap (Susp-fmap (∧Σ^-out Y X m)) $ swap-Σ∧-out (⊙Susp^ m X) Y s ⟩
    Susp-fmap (∧Σ^-out Y X m) (∧Σ-out Y (⊙Susp^ m X) (∧-swap (⊙Susp^ (S m) X) Y s)) =∎

  swap-∧Σ^-out : ∀ (n : ℕ)
    → Susp^-fmap n (∧-swap X Y) ∘ ∧Σ^-out X Y n ∼
      Σ^∧-out Y X n ∘ ∧-swap X (⊙Susp^ n Y)
  swap-∧Σ^-out O s = idp
  swap-∧Σ^-out (S n) s =
    Susp^-fmap (S n) (∧-swap X Y) (Susp-fmap (∧Σ^-out X Y n) (∧Σ-out X (⊙Susp^ n Y) s))
      =⟨ ! (Susp-fmap-∘ (Susp^-fmap n (∧-swap X Y)) (∧Σ^-out X Y n) (∧Σ-out X (⊙Susp^ n Y) s)) ⟩
    Susp-fmap (Susp^-fmap n (∧-swap X Y) ∘ ∧Σ^-out X Y n) (∧Σ-out X (⊙Susp^ n Y) s)
      =⟨ ap (λ f → Susp-fmap f (∧Σ-out X (⊙Susp^ n Y) s)) (λ= (swap-∧Σ^-out n)) ⟩
    Susp-fmap (Σ^∧-out Y X n ∘ ∧-swap X (⊙Susp^ n Y)) (∧Σ-out X (⊙Susp^ n Y) s)
      =⟨ Susp-fmap-∘ (Σ^∧-out Y X n) (∧-swap X (⊙Susp^ n Y)) (∧Σ-out X (⊙Susp^ n Y) s) ⟩
    Susp-fmap (Σ^∧-out Y X n) (Susp-fmap (∧-swap X (⊙Susp^ n Y)) (∧Σ-out X (⊙Susp^ n Y) s))
      =⟨ ap (Susp-fmap (Σ^∧-out Y X n)) $ swap-∧Σ-out X (⊙Susp^ n Y) s ⟩
    Susp-fmap (Σ^∧-out Y X n) (Σ∧-out (⊙Susp^ n Y) X (∧-swap X (⊙Susp (de⊙ (⊙Susp^ n Y))) s)) =∎

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  Σ^∧Σ^-out-swap : ∀ (m n : ℕ)
    → transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) ∘ Susp^-fmap (m + n) (∧-swap X Y) ∘ Σ^∧Σ^-out X Y m n ∼
      maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ∘ Σ^∧Σ^-out Y X n m ∘ ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y)
  Σ^∧Σ^-out-swap m n s =
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     Susp^-fmap (m + n) (∧-swap X Y) $
     Σ^∧Σ^-out X Y m n s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ! $ Susp^-+-natural m n (∧-swap X Y) $
         Susp^-fmap m (∧Σ^-out X Y n) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     Susp^-fmap m (Susp^-fmap n (∧-swap X Y)) $
     Susp^-fmap m (∧Σ^-out X Y n) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ap (coe (Susp^-+ m n {Y ∧ X})) $
         ! $ app= (Susp^-fmap-∘ m (Susp^-fmap n (∧-swap X Y)) (∧Σ^-out X Y n)) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     Susp^-fmap m (Susp^-fmap n (∧-swap X Y) ∘ ∧Σ^-out X Y n) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ap (coe (Susp^-+ m n {Y ∧ X})) $
         app= (ap (Susp^-fmap m) (λ= (swap-∧Σ^-out X Y n))) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     Susp^-fmap m (Σ^∧-out Y X n ∘ ∧-swap X (⊙Susp^ n Y)) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ap (coe (Susp^-+ m n {Y ∧ X})) $
         app= (Susp^-fmap-∘ m (Σ^∧-out Y X n) (∧-swap X (⊙Susp^ n Y))) $
         Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     Susp^-fmap m (Σ^∧-out Y X n) $
     Susp^-fmap m (∧-swap X (⊙Susp^ n Y)) $
     Σ^∧-out X (⊙Susp^ n Y) m s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ap (coe (Susp^-+ m n {Y ∧ X})) $
         ap (Susp^-fmap m (Σ^∧-out Y X n)) $
         swap-Σ^∧-out X (⊙Susp^ n Y) m s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     Susp^-fmap m (Σ^∧-out Y X n) $
     ∧Σ^-out (⊙Susp^ n Y) X m $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s)
      =⟨ ap (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         ap (coe (Susp^-+ m n {Y ∧ X})) $
         ∧Σ^-Σ^∧-out' Y X n m $
         ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s ⟩
    (transport (λ k → Susp^ k (Y ∧ X)) (+-comm m n) $
     coe (Susp^-+ m n {Y ∧ X}) $
     coe (Susp^-comm n m) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (∧Σ^-out Y X m) $
     Σ^∧-out Y (⊙Susp^ m X) n $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s)
      =⟨ ! $ coe-∙ (Susp^-+ m n {Y ∧ X}) (ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         coe (Susp^-comm n m) $
         odd-odd-Susp^-flip n m $
         Susp^-fmap n (∧Σ^-out Y X m) $
         Σ^∧-out Y (⊙Susp^ m X) n $
         ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s ⟩
    (coe (Susp^-+ m n {Y ∧ X} ∙ ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
     coe (Susp^-comm n m) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (∧Σ^-out Y X m) $
     Σ^∧-out Y (⊙Susp^ m X) n $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s)
      =⟨ ! $ coe-∙ (Susp^-comm n m) (Susp^-+ m n {Y ∧ X} ∙ ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
         odd-odd-Susp^-flip n m $
         Susp^-fmap n (∧Σ^-out Y X m) $
         Σ^∧-out Y (⊙Susp^ m X) n $
         ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s ⟩
    (coe (Susp^-comm n m ∙ Susp^-+ m n {Y ∧ X} ∙ ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n)) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (∧Σ^-out Y X m) $
     Σ^∧-out Y (⊙Susp^ m X) n $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s)
      =⟨ app= (ap coe (=ₛ-out p)) $
         odd-odd-Susp^-flip n m $
         Susp^-fmap n (∧Σ^-out Y X m) $
         Σ^∧-out Y (⊙Susp^ m X) n $
         ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s ⟩
    (coe (Susp^-+ n m {Y ∧ X}) $
     odd-odd-Susp^-flip n m $
     Susp^-fmap n (∧Σ^-out Y X m) $
     Σ^∧-out Y (⊙Susp^ m X) n $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s)
      =⟨ maybe-Susp^-flip-+ n m (and (odd n) (odd m)) (ap (λ k → and (odd k) (odd m))) $
         Susp^-fmap n (∧Σ^-out Y X m) $
         Σ^∧-out Y (⊙Susp^ m X) n $
         ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s ⟩
    (maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
     Σ^∧Σ^-out Y X n m $
     ∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) s) =∎
    where
    p : Susp^-comm n m ◃∙ Susp^-+ m n {Y ∧ X} ◃∙ ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n) ◃∎
        =ₛ Susp^-+ n m {Y ∧ X} ◃∎
    p =
      Susp^-comm n m ◃∙
      Susp^-+ m n {Y ∧ X} ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n) ◃∎
        =ₛ⟨ 0 & 1 & expand (Susp^-comm-seq n m) ⟩
      Susp^-+ n m ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm n m) ◃∙
      ! (Susp^-+ m n) ◃∙
      Susp^-+ m n ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n) ◃∎
        =ₛ⟨ 2 & 2 & seq-!-inv-l (Susp^-+ m n ◃∎) ⟩
      Susp^-+ n m ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm n m) ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm m n) ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (λ k → Susp^ k (Y ∧ X))) $
             set-path ℕ-level (+-comm m n) (! (+-comm n m)) ⟩
      Susp^-+ n m ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (+-comm n m) ◃∙
      ap (λ k → Susp^ k (Y ∧ X)) (! (+-comm n m)) ◃∎
        =ₛ⟨ 1 & 2 & ap-seq-=ₛ (λ k → Susp^ k (Y ∧ X)) $
                    seq-!-inv-r (+-comm n m ◃∎) ⟩
      Susp^-+ n m ◃∎ ∎ₛ
