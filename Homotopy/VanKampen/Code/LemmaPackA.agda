{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Pushout
open import Homotopy.VanKampen.Guide

module Homotopy.VanKampen.Code.LemmaPackA {i} (d : pushout-diag i)
  (l : legend i (pushout-diag.C d)) where

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation

  private
    module PackA1 (d : pushout-diag i)
      (l : legend i (pushout-diag.C d)) (n : legend.name l) where
      open pushout-diag d
      open legend l

      -- Code from A.
      open import Homotopy.VanKampen.SplitCode d l (f $ loc n)
      -- Code from B. F for `flipped'.
      import Homotopy.VanKampen.SplitCode (pushout-diag-flip d) l (g $ loc n) as F

      private
        ap⇒bp-split : (∀ {a₂} → code-a a₂ → F.code-b a₂)
                    × (∀ {b₂} → code-b b₂ → F.code-a b₂)
        ap⇒bp-split = code-rec-nondep
          F.code-b ⦃ λ _ → F.code-b-is-set _ ⦄
          F.code-a ⦃ λ _ → F.code-a-is-set _ ⦄
          (λ p → F.⟧a refl₀ F.a⟦ n ⟧b p)
          (λ n₁ pco p → pco F.a⟦ n₁ ⟧b p)
          (λ n₁ pco p → pco F.b⟦ n₁ ⟧a p)
          (λ n₁ pco → F.code-b-refl-refl n₁ pco)
          (λ n₁ pco → F.code-a-refl-refl n₁ pco)
          (λ n₁ pco n₂ r → F.code-ba-swap n₁ pco n₂ r)

      aa⇒ba : ∀ {a₂} → code-a a₂ → F.code-b a₂
      aa⇒ba = π₁ ap⇒bp-split
      ab⇒bb : ∀ {b₂} → code-b b₂ → F.code-a b₂
      ab⇒bb = π₂ ap⇒bp-split

  private
    module PackA2 (d : pushout-diag i)
      (l : legend i (pushout-diag.C d)) (n : legend.name l) where
      open pushout-diag d
      open legend l

      -- Code from A.
      open import Homotopy.VanKampen.SplitCode d l (f $ loc n)
      open PackA1 d l n public
      -- Code from B. F for `flipped'.
      private
        module F where
          open import Homotopy.VanKampen.SplitCode (pushout-diag-flip d) l (g $ loc n) public
          open PackA1 (pushout-diag-flip d) l n public

      private
        aba-glue-code-split : (∀ {a₂} (co : code-a a₂) → F.ab⇒bb (aa⇒ba co) ≡ co)
                            × (∀ {b₂} (co : code-b b₂) → F.aa⇒ba (ab⇒bb co) ≡ co)
      abstract
        aba-glue-code-split = code-rec
          (λ {a} co → F.ab⇒bb (aa⇒ba co) ≡ co)
          ⦃ λ _ → ≡-is-set $ code-a-is-set _ ⦄
          (λ {b} co → F.aa⇒ba (ab⇒bb co) ≡ co)
          ⦃ λ _ → ≡-is-set $ code-b-is-set _ ⦄
          (λ p →
            ⟧a refl₀ a⟦ n ⟧b refl₀ b⟦ n ⟧a p
                ≡⟨ code-a-merge n refl₀ p ⟩
            ⟧a refl₀ ∘₀ p
                ≡⟨ ap (λ x → ⟧a x) $ refl₀-left-unit p ⟩∎
            ⟧a p
                ∎)
          (λ n₁ {co} eq p → ap (λ x → x b⟦ n₁ ⟧a p) eq)
          (λ n₁ {co} eq p → ap (λ x → x a⟦ n₁ ⟧b p) eq)
          (λ _ _ → code-has-all-cells₂-a _ _)
          (λ _ _ → code-has-all-cells₂-b _ _)
          (λ _ _ _ _ → code-has-all-cells₂-a _ _)

      aba-glue-code-a : ∀ {a₂} (co : code-a a₂) → F.ab⇒bb (aa⇒ba co) ≡ co
      aba-glue-code-a = π₁ aba-glue-code-split
      aba-glue-code-b : ∀ {b₂} (co : code-b b₂) → F.aa⇒ba (ab⇒bb co) ≡ co
      aba-glue-code-b = π₂ aba-glue-code-split

  private
    module PackA3 (d : pushout-diag i)
      (l : legend i (pushout-diag.C d)) (n : legend.name l) where
      open pushout-diag d
      open legend l

      -- Code from A.
      open import Homotopy.VanKampen.SplitCode d l (f $ loc n)
      open PackA2 d l n public
      -- Code from B. F for `flipped'.
      private
        module F where
          open import Homotopy.VanKampen.SplitCode (pushout-diag-flip d) l (g $ loc n) public
          open PackA2 (pushout-diag-flip d) l n public

      flipped-code : P → Set i
      flipped-code = F.code ◯ pushout-flip

      private
        ap⇒bp-glue : ∀ c → transport (λ p → code p → flipped-code p) (glue c) aa⇒ba ≡ ab⇒bb
      abstract
        ap⇒bp-glue = loc-fiber-rec l
          (λ c → transport (λ p → code p → flipped-code p) (glue c) aa⇒ba ≡ ab⇒bb)
          ⦃ λ _ → Π-is-set (λ _ → F.code-a-is-set _) _ _ ⦄
          (λ n → funext λ co →
            transport (λ p → code p → flipped-code p) (glue $ loc n) aa⇒ba co
                ≡⟨ trans-→ code flipped-code (glue $ loc n) aa⇒ba co ⟩
            transport flipped-code (glue $ loc n)
              (aa⇒ba $ transport code (! $ glue $ loc n) co)
                ≡⟨ ap (λ x → transport flipped-code (glue $ loc n) $ aa⇒ba x)
                    $ trans-code-!glue-loc n co ⟩
            transport flipped-code (glue $ loc n) (aa⇒ba $ b⇒a n co)
                ≡⟨ refl ⟩
            transport flipped-code (glue $ loc n) (F.a⇒b n $ ab⇒bb co)
                ≡⟨ ! $ trans-ap F.code pushout-flip (glue $ loc n)
                     $ F.a⇒b n $ ab⇒bb co ⟩
            transport F.code (ap pushout-flip $ glue $ loc n) (F.a⇒b n $ ab⇒bb co)
                ≡⟨ ap (λ x → transport F.code x $ F.a⇒b n $ ab⇒bb co)
                      $ pushout-β-glue-nondep _ right left (! ◯ glue) $ loc n ⟩
            transport F.code (! $ glue $ loc n) (F.a⇒b n $ ab⇒bb co)
                ≡⟨ F.trans-code-!glue-loc n (F.a⇒b n $ ab⇒bb co) ⟩
            F.b⇒a n (F.a⇒b n $ ab⇒bb co)
                ≡⟨ F.code-a-refl-refl n $ ab⇒bb co ⟩∎
            ab⇒bb co
                ∎)

      ap⇒bp : ∀ {p} → code p → flipped-code p
      ap⇒bp {p} = pushout-rec
        (λ x → code x → flipped-code x)
        (λ _ → aa⇒ba)
        (λ _ → ab⇒bb)
        ap⇒bp-glue
        p

  open PackA3 d l public
