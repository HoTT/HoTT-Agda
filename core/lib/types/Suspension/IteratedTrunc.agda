{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.FunctionSeq
open import lib.types.Pointed
open import lib.types.Suspension.Core
open import lib.types.Suspension.Iterated
open import lib.types.Suspension.Trunc
open import lib.types.TLevel
open import lib.types.Truncation

module lib.types.Suspension.IteratedTrunc where

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
