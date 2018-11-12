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
  ⊙maybe-Susp^-flip-+ : ∀ {i} {X : Ptd i} (m n : ℕ) (b : Bool)
    → (m == 0 → b == false)
    → ⊙coe (⊙Susp^-+ m n {X}) ◃⊙∘
      ⊙maybe-Susp^-flip {X = ⊙Susp^ n X} m b ◃⊙idf
      =⊙∘
      ⊙maybe-Susp^-flip (m + n) b ◃⊙∘
      ⊙coe (⊙Susp^-+ m n) ◃⊙idf
  ⊙maybe-Susp^-flip-+ O O b h = =⊙∘-in idp
  ⊙maybe-Susp^-flip-+ O (S n) true h = ⊥-elim (Bool-true≠false (h idp))
  ⊙maybe-Susp^-flip-+ O (S n) false h = =⊙∘-in idp
  ⊙maybe-Susp^-flip-+ {X = X} (S m) n true h =
    ⊙coe (ap ⊙Susp (Susp^-+ m n)) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ n X)) ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ! p ⟩
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-+ m n))) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ n X)) ◃⊙idf
      =⊙∘⟨ =⊙∘-in $ ! $
           ⊙Susp-flip-natural (⊙coe (⊙Susp^-+ m n)) ⟩
    ⊙Susp-flip (⊙Susp^ (m + n) X) ◃⊙∘
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-+ m n))) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & p ⟩
    ⊙Susp-flip (⊙Susp^ (m + n) X) ◃⊙∘
    ⊙coe (ap ⊙Susp (Susp^-+ m n)) ◃⊙idf ∎⊙∘
    where
    p : ⊙Susp-fmap (fst (⊙coe (⊙Susp^-+ m n {X}))) ==
        ⊙coe (ap ⊙Susp (Susp^-+ m n))
    p =
      ap (⊙Susp-fmap ∘ coe) (de⊙-⊙Susp^-+ m n {X}) ∙
      ! (⊙transport-⊙Susp (Susp^-+ m n)) ∙
      ⊙transport-⊙coe ⊙Susp (Susp^-+ m n)
  ⊙maybe-Susp^-flip-+ (S m) n false h = =⊙∘-in $ ! $ ⊙λ= $ ⊙∘-unit-l _

  ⊙maybe-Susp^-flip-comm : ∀ {i} {X : Ptd i} (m n : ℕ) (b : Bool)
    → (m == 0 → b == false)
    → (n == 0 → b == false)
    → ⊙coe (⊙Susp^-comm m n {X = X}) ◃⊙∘
      ⊙maybe-Susp^-flip {X = ⊙Susp^ n X} m b ◃⊙idf
      =⊙∘
      ⊙maybe-Susp^-flip {X = ⊙Susp^ m X} n b ◃⊙∘
      ⊙coe (⊙Susp^-comm m n) ◃⊙idf
  ⊙maybe-Susp^-flip-comm O O b h₁ h₂ = =⊙∘-in (! (⊙λ= (⊙∘-unit-l (⊙coe (⊙Susp^-comm 0 0)))))
  ⊙maybe-Susp^-flip-comm O (S _) true  h₁ h₂ = ⊥-elim (Bool-true≠false (h₁ idp))
  ⊙maybe-Susp^-flip-comm O (S _) false h₁ h₂ = =⊙∘-in (! (⊙λ= (⊙∘-unit-l _)))
  ⊙maybe-Susp^-flip-comm (S m) O true  h₁ h₂ = ⊥-elim (Bool-true≠false (h₂ idp))
  ⊙maybe-Susp^-flip-comm (S m) O false h₁ h₂ = =⊙∘-in (! (⊙λ= (⊙∘-unit-l _)))
  ⊙maybe-Susp^-flip-comm {X = X} (S m) (S n) true h₁ h₂ =
    ⊙coe (⊙Susp^-comm (S m) (S n)) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ (S n) X)) ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & p ⟩
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) ∙ ⊙Susp^-comm 1 n))) ◃⊙∘
    ⊙Susp-flip (⊙Susp^ m (⊙Susp^ (S n) X)) ◃⊙idf
      =⊙∘⟨ =⊙∘-in $ ! $
           ⊙Susp-flip-natural (⊙coe (⊙Susp^-comm m (S n) ∙ ⊙Susp^-comm 1 n)) ⟩
    ⊙Susp-flip (⊙Susp^ n (⊙Susp^ (S m) X)) ◃⊙∘
    ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) ∙ ⊙Susp^-comm 1 n))) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ! p ⟩
    ⊙Susp-flip (⊙Susp^ n (⊙Susp^ (S m) X)) ◃⊙∘
    ⊙Susp^-swap (S m) (S n) ◃⊙idf ∎⊙∘
    where
    p : ⊙Susp^-swap (S m) (S n) {X} ==
        ⊙Susp-fmap (fst (⊙coe (⊙Susp^-comm m (S n) {X} ∙ ⊙Susp^-comm 1 n {⊙Susp^ m X})))
    p =
      ap ⊙coe (⊙Susp^-comm-S-S m n) ∙
      ! (⊙transport-⊙coe ⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n)) ∙
      ⊙transport-⊙Susp (Susp^-comm m (S n) ∙ Susp^-comm 1 n) ∙
      ! (ap (⊙Susp-fmap ∘ coe) (ap2 _∙_ (de⊙-⊙Susp^-comm m (S n)) (de⊙-⊙Susp^-comm 1 n))) ∙
      ap (⊙Susp-fmap ∘ coe) (∙-ap de⊙ (⊙Susp^-comm m (S n)) (⊙Susp^-comm 1 n))
  ⊙maybe-Susp^-flip-comm (S m) (S n) false h₁ h₂ = =⊙∘-in (! (⊙λ= (⊙∘-unit-l _)))

⊙∧Σ-Σ^∧-out : ∀ {i} {j} (X : Ptd i) (Y : Ptd j) (m : ℕ)
  → ⊙Susp-fmap (∧Σ^-out X Y m) ◃⊙∘
    ⊙Σ∧-out X (⊙Susp^ m Y) ◃⊙idf
    =⊙∘
    ⊙Susp^-swap m 1 {X = X ⊙∧ Y} ◃⊙∘
    ⊙maybe-Susp^-flip m (odd m) ◃⊙∘
    ⊙Susp^-fmap m (⊙Σ∧-out X Y) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y m ◃⊙idf
⊙∧Σ-Σ^∧-out X Y 0 =
  ⊙Susp-fmap (idf (X ∧ Y)) ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙idf
    =⊙∘⟨ 0 & 1 & ⊙Susp-fmap-idf _ ⟩
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙idf
    =⊙∘⟨ 0 & 0 & ⊙contract ⟩
  ⊙idf _ ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙idf
    =⊙∘₁⟨ 0 & 1 & ap ⊙coe (! (⊙Susp^-comm-0-l 1 (X ⊙∧ Y))) ⟩
  ⊙Susp^-swap 0 1 ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙idf
    =⊙∘⟨ 1 & 0 & ⊙contract ⟩
  ⊙Susp^-swap 0 1 ◃⊙∘
  ⊙idf _ ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙idf
    =⊙∘⟨ 3 & 0 & ⊙contract ⟩
  ⊙Susp^-swap 0 1 ◃⊙∘
  ⊙idf _ ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ 0 Y) ◃⊙∘
  ⊙idf _ ◃⊙idf ∎⊙∘
⊙∧Σ-Σ^∧-out X Y (S m) =
  ⊙Susp-fmap (∧Σ^-out X Y (S m)) ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ (S m) Y) ◃⊙idf
    =⊙∘⟨ 0 & 1 & ⊙Susp-fmap-seq-∘ (Susp-fmap (∧Σ^-out X Y m) ◃∘
                                   ∧Σ-out X (⊙Susp^ m Y) ◃idf) ⟩
  ⊙Susp^-fmap 2 (⊙∧Σ^-out X Y m) ◃⊙∘
  ⊙Susp-fmap (∧Σ-out X (⊙Susp^ m Y)) ◃⊙∘
  ⊙Σ∧-out X (⊙Susp^ (S m) Y) ◃⊙idf
    =⊙∘⟨ 1 & 2 & ⊙∧Σ-Σ∧-out X (⊙Susp^ m Y) ⟩
  ⊙Susp^-fmap 2 (⊙∧Σ^-out X Y m) ◃⊙∘
  ⊙Susp-flip (⊙Susp (X ∧ ⊙Susp^ m Y)) ◃⊙∘
  ⊙Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) ◃⊙∘
  ⊙∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) ◃⊙idf
    =⊙∘⟨ 0 & 2 & =⊙∘-in {gs = ⊙Susp-flip (⊙Susp (Susp^ m (X ∧ Y))) ◃⊙∘
                              ⊙Susp^-fmap 2 (⊙∧Σ^-out X Y m) ◃⊙idf} $
                 ! (⊙Susp-flip-natural (⊙Susp-fmap (∧Σ^-out X Y m))) ⟩
  ⊙Susp-flip (⊙Susp (Susp^ m (X ∧ Y))) ◃⊙∘
  ⊙Susp^-fmap 2 (⊙∧Σ^-out X Y m) ◃⊙∘
  ⊙Susp-fmap (Σ∧-out X (⊙Susp^ m Y)) ◃⊙∘
  ⊙∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) ◃⊙idf
    =⊙∘⟨ 1 & 2 & ⊙Susp-fmap-seq-=⊙∘ (de⊙-seq-=⊙∘ (⊙∧Σ-Σ^∧-out X Y m)) ⟩
  ⊙Susp-flip (⊙Susp (Susp^ m (X ∧ Y))) ◃⊙∘
  ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm m 1))) ◃⊙∘
  ⊙Susp-fmap (fst (⊙maybe-Susp^-flip m (odd m))) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙Susp-fmap (∧Σ^-out (⊙Susp (de⊙ X)) Y m) ◃⊙∘
  ⊙∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) ◃⊙idf
    =⊙∘⟨ 0 & 2 & =⊙∘-in {gs = ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm m 1))) ◃⊙∘
                              ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙idf} $
                 ⊙Susp-flip-natural (⊙coe (⊙Susp^-comm m 1)) ⟩
  ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm m 1))) ◃⊙∘
  ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙∘
  ⊙Susp-fmap (fst (⊙maybe-Susp^-flip m (odd m))) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙Susp-fmap (∧Σ^-out (⊙Susp (de⊙ X)) Y m) ◃⊙∘
  ⊙∧Σ-out (⊙Susp (de⊙ X)) (⊙Susp^ m Y) ◃⊙idf
    =⊙∘⟨ 4 & 2 & ⊙contract ⟩
  ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm m 1))) ◃⊙∘
  ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙∘
  ⊙Susp-fmap (fst (⊙maybe-Susp^-flip m (odd m))) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) ◃⊙idf
    =⊙∘₁⟨ 0 & 1 & ! (⊙transport-⊙Susp (ap de⊙ (⊙Susp^-comm m 1))) ∙
                  ap (⊙transport ⊙Susp) (de⊙-⊙Susp^-comm m 1) ∙
                  ⊙transport-⊙coe ⊙Susp (Susp^-comm m 1) ∙
                  ap ⊙coe (! (⊙Susp^-comm-S-1 m {X ⊙∧ Y})) ⟩
  ⊙coe (⊙Susp^-comm (S m) 1) ◃⊙∘
  ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙∘
  ⊙Susp-fmap (fst (⊙maybe-Susp^-flip m (odd m))) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) ◃⊙idf
    =⊙∘₁⟨ 2 & 1 & ap ⊙Susp-fmap (de⊙-⊙maybe-Susp^-flip m (odd m)) ⟩
  ⊙coe (⊙Susp^-comm (S m) 1) ◃⊙∘
  ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙∘
  ⊙Susp-fmap (maybe-Susp^-flip m (odd m)) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) ◃⊙idf
    =⊙∘₁⟨ 2 & 1 & ⊙Susp-fmap-maybe-Susp^-flip m (odd m) (ap odd) ⟩
  ⊙coe (⊙Susp^-comm (S m) 1) ◃⊙∘
  ⊙Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) ◃⊙∘
  ⊙maybe-Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) (odd m) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) ◃⊙idf
    =⊙∘⟨ 1 & 2 & ⊙maybe-Susp-flip-flip _ true (odd m) ⟩
  ⊙coe (⊙Susp^-comm (S m) 1) ◃⊙∘
  ⊙maybe-Susp-flip (⊙Susp^ m (⊙Susp (X ∧ Y))) (odd (S m)) ◃⊙∘
  ⊙Susp^-fmap (S m) (⊙Σ∧-out X Y) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp (de⊙ X)) Y (S m) ◃⊙idf ∎⊙∘

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙∧Σ^-Σ^∧-out : ∀ (m n : ℕ)
    → ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
      ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
      =⊙∘
      ⊙coe (⊙Susp^-comm n m) ◃⊙∘
      ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
      ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
      ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
  ⊙∧Σ^-Σ^∧-out O n =
    ⊙∧Σ^-out X Y n ◃⊙∘
    ⊙idf _ ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand ⊙idf-seq ⟩
    ⊙∧Σ^-out X Y n ◃⊙idf
      =⊙∘⟨ 0 & 0 & !⊙∘ (⊙Susp^-fmap-idf n (X ⊙∧ Y)) ⟩
    ⊙Susp^-fmap n (⊙idf (X ⊙∧ Y)) ◃⊙∘
    ⊙∧Σ^-out X Y n ◃⊙idf
      =⊙∘₁⟨ 0 & 0 & ! (⊙maybe-Susp^-flip-false n) ⟩
    ⊙maybe-Susp^-flip n false ◃⊙∘
    ⊙Susp^-fmap n (⊙idf (X ⊙∧ Y)) ◃⊙∘
    ⊙∧Σ^-out X Y n ◃⊙idf
      =⊙∘₁⟨ 0 & 0 & ap ⊙coe (! (⊙Susp^-comm-0-r n _)) ⟩
    ⊙coe (⊙Susp^-comm n O) ◃⊙∘
    ⊙maybe-Susp^-flip n false ◃⊙∘
    ⊙Susp^-fmap n (⊙idf (X ⊙∧ Y)) ◃⊙∘
    ⊙∧Σ^-out X Y n ◃⊙idf ∎⊙∘
  ⊙∧Σ^-Σ^∧-out (S m) n =
    ⊙Susp^-fmap (S m) (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) (S m) ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand (⊙Susp-fmap (Σ^∧-out X (⊙Susp^ n Y) m) ◃⊙∘
                            ⊙Σ∧-out (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf) ⟩
    ⊙Susp^-fmap (S m) (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Susp-fmap (Σ^∧-out X (⊙Susp^ n Y) m) ◃⊙∘
    ⊙Σ∧-out (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙Susp-fmap-seq-=⊙∘ (de⊙-seq-=⊙∘ (⊙∧Σ^-Σ^∧-out m n)) ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙maybe-Susp^-flip n (and (odd m) (odd n)))) ◃⊙∘
    ⊙Susp-fmap (Susp^-fmap n (Σ^∧-out X Y m)) ◃⊙∘
    ⊙Susp-fmap (∧Σ^-out (⊙Susp^ m X) Y n) ◃⊙∘
    ⊙Σ∧-out (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
      =⊙∘⟨ 3 & 2 & ⊙∧Σ-Σ^∧-out (⊙Susp^ m X) Y n ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙maybe-Susp^-flip n (and (odd m) (odd n)))) ◃⊙∘
    ⊙Susp-fmap (Susp^-fmap n (Σ^∧-out X Y m)) ◃⊙∘
    ⊙Susp^-swap n 1 ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ∧-out (⊙Susp^ m X) Y) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘⟨ 2 & 2 & !⊙∘ $ ⊙Susp^-swap-natural n 1 (⊙Σ^∧-out X Y m) ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙maybe-Susp^-flip n (and (odd m) (odd n)))) ◃⊙∘
    ⊙Susp^-swap n 1 ◃⊙∘
    ⊙Susp^-fmap n (⊙Susp-fmap (Σ^∧-out X Y m)) ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ∧-out (⊙Susp^ m X) Y) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘⟨ 3 & 2 & ⊙maybe-Susp^-flip-natural-=⊙∘ (⊙Susp-fmap (Σ^∧-out X Y m)) n (odd n) ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙maybe-Susp^-flip n (and (odd m) (odd n)))) ◃⊙∘
    ⊙Susp^-swap n 1 ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Susp-fmap (Σ^∧-out X Y m)) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ∧-out (⊙Susp^ m X) Y) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘₁⟨ 4 & 2 & ! $ ⊙Susp^-fmap-∘ n (⊙Susp-fmap (Σ^∧-out X Y m)) (⊙Σ∧-out (⊙Susp^ m X) Y) ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙Susp-fmap (fst (⊙maybe-Susp^-flip n (and (odd m) (odd n)))) ◃⊙∘
    ⊙Susp^-swap n 1 ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙maybe-Susp^-flip-⊙Susp^-comm _ n 1 (and (odd m) (odd n)) ⟩
    ⊙Susp-fmap (coe (ap de⊙ (⊙Susp^-comm n m))) ◃⊙∘
    ⊙coe (⊙Susp^-comm n 1) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ! (⊙transport-⊙Susp (ap de⊙ (⊙Susp^-comm n m))) ∙
                    ⊙transport-⊙coe ⊙Susp (ap de⊙ (⊙Susp^-comm n m)) ∙
                    ap (⊙coe ∘ ap ⊙Susp) (de⊙-⊙Susp^-comm n m) ⟩
    ⊙coe (ap ⊙Susp (Susp^-comm n m)) ◃⊙∘
    ⊙coe (⊙Susp^-comm n 1) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘₁⟨ 0 & 2 & ! (=⊙∘-out (⊙coe-∙ (⊙Susp^-comm n 1) (ap ⊙Susp (Susp^-comm n m)))) ∙
                    ap ⊙coe (! (=ₛ-out (⊙Susp^-comm-S-r n m))) ⟩
    ⊙coe (⊙Susp^-comm n (S m)) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙maybe-Susp^-flip n (odd n) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙maybe-Susp^-flip-flip n (and (odd m) (odd n)) (odd n) ⟩
    ⊙coe (⊙Susp^-comm n (S m)) ◃⊙∘
    ⊙maybe-Susp^-flip n (xor (and (odd m) (odd n)) (odd n)) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ap (⊙maybe-Susp^-flip n) (table (odd m) (odd n)) ⟩
    ⊙coe (⊙Susp^-comm n (S m)) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd (S m)) (odd n)) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y (S m)) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp (de⊙ (⊙Susp^ m X))) Y n ◃⊙idf ∎⊙∘
    where
    table : ∀ (b c : Bool) → xor (and b c) c == and (negate b) c
    table true  true  = idp
    table true  false = idp
    table false true  = idp
    table false false = idp

  ⊙∧Σ^-Σ^∧-out' : ∀ (m n : ℕ)
    → ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
      ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
      =⊙∘
      ⊙coe (⊙Susp^-comm m n) ◃⊙∘
      ⊙maybe-Susp^-flip m (and (odd m) (odd n)) ◃⊙∘
      ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
      ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
  ⊙∧Σ^-Σ^∧-out' m n =
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
      =⊙∘₁⟨ 0 & 0 & ! (⊙maybe-Susp^-flip-false n) ∙
                    ap (⊙maybe-Susp^-flip n) (! (xor-diag (and (odd m) (odd n)))) ⟩
    ⊙maybe-Susp^-flip n (xor (and (odd m) (odd n)) (and (odd m) (odd n))) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
      =⊙∘⟨ 0 & 1 & !⊙∘ $ ⊙maybe-Susp^-flip-flip n (and (odd m) (odd n)) (and (odd m) (odd n)) ⟩
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
      =⊙∘⟨ 1 & 0 & =⊙∘-in {gs = ⊙coe (! (⊙Susp^-comm n m)) ◃⊙∘
                                ⊙coe (⊙Susp^-comm n m) ◃⊙idf} $
           ap ⊙coe (! (!-inv-r (⊙Susp^-comm n m))) ∙
           =⊙∘-out (⊙coe-∙ (⊙Susp^-comm n m) (! (⊙Susp^-comm n m))) ⟩
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙coe (! (⊙Susp^-comm n m)) ◃⊙∘
    ⊙coe (⊙Susp^-comm n m) ◃⊙∘
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙Susp^-fmap n (⊙Σ^∧-out X Y m) ◃⊙∘
    ⊙∧Σ^-out (⊙Susp^ m X) Y n ◃⊙idf
      =⊙∘⟨ 2 & 4 & !⊙∘ $ ⊙∧Σ^-Σ^∧-out m n ⟩
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙coe (! (⊙Susp^-comm n m)) ◃⊙∘
    ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ap ⊙coe (⊙Susp^-comm-! n m) ⟩
    ⊙maybe-Susp^-flip n (and (odd m) (odd n)) ◃⊙∘
    ⊙coe (⊙Susp^-comm m n) ◃⊙∘
    ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
      =⊙∘⟨ 0 & 2 & !⊙∘ $
           ⊙maybe-Susp^-flip-comm m n (and (odd m) (odd n))
             (ap (λ k → and (odd k) (odd n)))
             (λ p → ap (and (odd m) ∘ odd) p ∙ and-false-r (odd m)) ⟩
    ⊙coe (⊙Susp^-comm m n) ◃⊙∘
    ⊙maybe-Susp^-flip m (and (odd m) (odd n)) ◃⊙∘
    ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf ∎⊙∘

  ⊙Σ^∧Σ^-out-seq : ∀ (m n : ℕ) → (⊙Susp^ m X ⊙∧ ⊙Susp^ n Y) ⊙–→ ⊙Susp^ (m + n) (X ⊙∧ Y)
  ⊙Σ^∧Σ^-out-seq m n =
    ⊙coe (⊙Susp^-+ m n {X ⊙∧ Y}) ◃⊙∘
    ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
    ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf

  ⊙Σ^∧Σ^-out : ∀ (m n : ℕ) → ⊙Susp^ m X ⊙∧ ⊙Susp^ n Y ⊙→ ⊙Susp^ (m + n) (X ⊙∧ Y)
  ⊙Σ^∧Σ^-out m n = ⊙compose (⊙Σ^∧Σ^-out-seq m n)

  swap-⊙Σ^∧-out : ∀ (m : ℕ)
    → ⊙Susp^-fmap m (⊙∧-swap X Y) ◃⊙∘
      ⊙Σ^∧-out X Y m ◃⊙idf
      =⊙∘
      ⊙∧Σ^-out Y X m ◃⊙∘
      ⊙∧-swap (⊙Susp^ m X) Y ◃⊙idf
  swap-⊙Σ^∧-out O = =⊙∘-in $ ! $ ⊙λ= $ ⊙∘-unit-l (⊙∧-swap X Y)
  swap-⊙Σ^∧-out (S m) =
    ⊙Susp^-fmap (S m) (⊙∧-swap X Y) ◃⊙∘
    ⊙Σ^∧-out X Y (S m) ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand (⊙Susp-fmap (Σ^∧-out X Y m) ◃⊙∘
                            ⊙Σ∧-out (⊙Susp^ m X) Y ◃⊙idf) ⟩
    ⊙Susp^-fmap (S m) (⊙∧-swap X Y) ◃⊙∘
    ⊙Susp-fmap (Σ^∧-out X Y m) ◃⊙∘
    ⊙Σ∧-out (⊙Susp^ m X) Y ◃⊙idf
      =⊙∘⟨ 0 & 2 &
           ⊙Susp-fmap-seq-=⊙∘ (de⊙-seq-=⊙∘ (swap-⊙Σ^∧-out m)) ⟩
    ⊙Susp-fmap (∧Σ^-out Y X m) ◃⊙∘
    ⊙Susp-fmap (∧-swap (⊙Susp^ m X) Y) ◃⊙∘
    ⊙Σ∧-out (⊙Susp^ m X) Y ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙swap-Σ∧-out (⊙Susp^ m X) Y ⟩
    ⊙Susp-fmap (∧Σ^-out Y X m) ◃⊙∘
    ⊙∧Σ-out Y (⊙Susp^ m X) ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ (⊙Susp^ m X))) Y ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙contract ⟩
    ⊙∧Σ^-out Y X (S m) ◃⊙∘
    ⊙∧-swap (⊙Susp^ (S m) X) Y ◃⊙idf ∎⊙∘

  swap-⊙∧Σ^-out : ∀ (n : ℕ)
    → ⊙Susp^-fmap n (⊙∧-swap X Y) ◃⊙∘
      ⊙∧Σ^-out X Y n ◃⊙idf
      =⊙∘
      ⊙Σ^∧-out Y X n ◃⊙∘
      ⊙∧-swap X (⊙Susp^ n Y) ◃⊙idf
  swap-⊙∧Σ^-out O = =⊙∘-in $ ! $ ⊙λ= $ ⊙∘-unit-l (⊙∧-swap X Y)
  swap-⊙∧Σ^-out (S n) =
    ⊙Susp^-fmap (S n) (⊙∧-swap X Y) ◃⊙∘
    ⊙∧Σ^-out X Y (S n) ◃⊙idf
      =⊙∘⟨ 1 & 1 & ⊙expand (⊙Susp-fmap (∧Σ^-out X Y n) ◃⊙∘
                            ⊙∧Σ-out X (⊙Susp^ n Y) ◃⊙idf) ⟩
    ⊙Susp^-fmap (S n) (⊙∧-swap X Y) ◃⊙∘
    ⊙Susp-fmap (∧Σ^-out X Y n) ◃⊙∘
    ⊙∧Σ-out X (⊙Susp^ n Y) ◃⊙idf
      =⊙∘⟨ 0 & 2 &
           ⊙Susp-fmap-seq-=⊙∘ (de⊙-seq-=⊙∘ (swap-⊙∧Σ^-out n))⟩
    ⊙Susp-fmap (fst (⊙Σ^∧-out Y X n)) ◃⊙∘
    ⊙Susp-fmap (fst (⊙∧-swap X (⊙Susp^ n Y))) ◃⊙∘
    ⊙∧Σ-out X (⊙Susp^ n Y) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙swap-∧Σ-out X (⊙Susp^ n Y) ⟩
    ⊙Susp-fmap (fst (⊙Σ^∧-out Y X n)) ◃⊙∘
    ⊙Σ∧-out (⊙Susp^ n Y) X ◃⊙∘
    ⊙∧-swap X (⊙Susp (de⊙ (⊙Susp^ n Y))) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙contract ⟩
    ⊙Σ^∧-out Y X (S n) ◃⊙∘
    ⊙∧-swap X (⊙Susp^ (S n) Y) ◃⊙idf ∎⊙∘

⊙Σ^∧Σ^-out-swap : ∀ {i} {j} (X : Ptd i) (Y : Ptd j) (m n : ℕ)
  → ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
    ⊙Susp^-fmap (m + n) (⊙∧-swap X Y) ◃⊙∘
    ⊙Σ^∧Σ^-out X Y m n ◃⊙idf
    =⊙∘
    ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
    ⊙Σ^∧Σ^-out Y X n m ◃⊙∘
    ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
⊙Σ^∧Σ^-out-swap X Y m n =
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap X Y) ◃⊙∘
  ⊙Σ^∧Σ^-out X Y m n ◃⊙idf
    =⊙∘⟨ 2 & 1 & ⊙expand (⊙Σ^∧Σ^-out-seq X Y m n) ⟩
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap X Y) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
  ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
    =⊙∘⟨ 1 & 2 & =⊙∘-in {gs = ⊙coe (⊙Susp^-+ m n) ◃⊙∘
                              ⊙Susp^-fmap m (⊙Susp^-fmap n (⊙∧-swap X Y)) ◃⊙idf} $
         ! $ ⊙Susp^-+-natural m n (⊙∧-swap X Y) ⟩
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙Susp^-fmap m (⊙Susp^-fmap n (⊙∧-swap X Y)) ◃⊙∘
  ⊙Susp^-fmap m (⊙∧Σ^-out X Y n) ◃⊙∘
  ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
    =⊙∘⟨ 2 & 2 & ⊙Susp^-fmap-seq-=⊙∘ m $ swap-⊙∧Σ^-out X Y n ⟩
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙Susp^-fmap m (⊙Σ^∧-out Y X n) ◃⊙∘
  ⊙Susp^-fmap m (⊙∧-swap X (⊙Susp^ n Y)) ◃⊙∘
  ⊙Σ^∧-out X (⊙Susp^ n Y) m ◃⊙idf
    =⊙∘⟨ 3 & 2 & swap-⊙Σ^∧-out X (⊙Susp^ n Y) m ⟩
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙Susp^-fmap m (⊙Σ^∧-out Y X n) ◃⊙∘
  ⊙∧Σ^-out (⊙Susp^ n Y) X m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
    =⊙∘⟨ 2 & 2 & ⊙∧Σ^-Σ^∧-out' Y X n m ⟩
  ⊙transport (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙coe (⊙Susp^-comm n m) ◃⊙∘
  ⊙maybe-Susp^-flip n (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap n (⊙∧Σ^-out Y X m) ◃⊙∘
  ⊙Σ^∧-out Y (⊙Susp^ m X) n ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
    =⊙∘₁⟨ 0 & 1 & ⊙transport-⊙coe (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ⟩
  ⊙coe (ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n)) ◃⊙∘
  ⊙coe (⊙Susp^-+ m n) ◃⊙∘
  ⊙coe (⊙Susp^-comm n m) ◃⊙∘
  ⊙maybe-Susp^-flip n (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap n (⊙∧Σ^-out Y X m) ◃⊙∘
  ⊙Σ^∧-out Y (⊙Susp^ m X) n ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
    =⊙∘⟨ 0 & 3 & ⊙coe-seq-=ₛ p ⟩
  ⊙coe (⊙Susp^-+ n m) ◃⊙∘
  ⊙maybe-Susp^-flip n (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap n (⊙∧Σ^-out Y X m) ◃⊙∘
  ⊙Σ^∧-out Y (⊙Susp^ m X) n ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
    =⊙∘⟨ 0 & 2 & ⊙maybe-Susp^-flip-+ n m (and (odd n) (odd m))
           (ap (λ k → and (odd k) (odd m))) ⟩
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙coe (⊙Susp^-+ n m) ◃⊙∘
  ⊙Susp^-fmap n (⊙∧Σ^-out Y X m) ◃⊙∘
  ⊙Σ^∧-out Y (⊙Susp^ m X) n ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf
    =⊙∘⟨ 1 & 3 & ⊙contract ⟩
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Σ^∧Σ^-out Y X n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m X) (⊙Susp^ n Y) ◃⊙idf ∎⊙∘
  where
  p : ⊙Susp^-comm n m ◃∙
      ⊙Susp^-+ m n {Y ⊙∧ X} ◃∙
      ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃∎
      =ₛ
      ⊙Susp^-+ n m {Y ⊙∧ X} ◃∎
  p =
    ⊙Susp^-comm n m ◃∙
    ⊙Susp^-+ m n {Y ⊙∧ X} ◃∙
    ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃∎
      =ₛ⟨ 0 & 1 & expand (⊙Susp^-comm-seq n m) ⟩
    ⊙Susp^-+ n m ◃∙
    ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm n m) ◃∙
    ! (⊙Susp^-+ m n) ◃∙
    ⊙Susp^-+ m n ◃∙
    ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃∎
      =ₛ⟨ 2 & 2 & seq-!-inv-l (⊙Susp^-+ m n ◃∎) ⟩
    ⊙Susp^-+ n m ◃∙
    ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm n m) ◃∙
    ap (λ k → ⊙Susp^ k (Y ⊙∧ X)) (+-comm m n) ◃∎
      =ₛ⟨ 1 & 2 & ap-seq-=ₛ (λ k → ⊙Susp^ k (Y ⊙∧ X)) $
          =ₛ-in {s = +-comm n m ◃∙ +-comm m n ◃∎} {t = []} $
          set-path ℕ-level _ _ ⟩
    ⊙Susp^-+ n m ◃∎ ∎ₛ
