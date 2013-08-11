{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IteratedSuspension where

Susp^ : ∀ {i} (n : ℕ) → Type i → Type i
Susp^ O A = A
Susp^ (S n) A = Suspension (Susp^ n A)

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

north^ : ∀ {i} (n : ℕ) {A : Type i} (a : A) → Susp^ n A
north^ O a = a
north^ (S n) {A = A} a = north (Susp^ n A)

Susp^-conn : ∀ {i} (n : ℕ) {A : Type i} {m : ℕ₋₂}
  → is-connected m A → is-connected ((n -2) +2+ m) (Susp^ n A)
Susp^-conn O cA = cA
Susp^-conn (S n) cA = Susp-conn (Susp^-conn n cA)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)

{- π (S k) (Susp^ (S n) A) (north^ (S n) a) == π k (Susp^ n A) (north^ n a),
   where n = S n' and k = S k' -}
module Susp^Stable {i} (X : Ptd i) (cX : is-connected ⟨0⟩ (fst X))
  (n' : ℕ) (k' : ℕ) (kle : S k' ≤ (S n') *2) where
  
  {- need k,n ≥ 1 -}
  k : ℕ
  k = S k'

  n : ℕ
  n = S n'

  {- some numeric computations -}
  private
    kle' : ⟨ k ⟩ ≤T S ((n -2) +2+ S (n -2))
    kle' = ≤T-trans (⟨⟩-monotone-≤ kle) (inl (lemma n'))
      where lemma : (n' : ℕ) → ⟨ S n' *2 ⟩ == S ((S n' -2) +2+ S (S n' -2))
            lemma O = idp
            lemma (S n') = ap S (ap S (lemma n') 
                                 ∙ ! (+2+-βr (S (S n') -2) (S (S n') -2)))


    nlemma₁ : (n : ℕ) → (n -2) +2+ ⟨0⟩ == S (S (n -2))
    nlemma₁ n = +2+-comm (n -2) ⟨0⟩

    nlemma₂ : (k : ℕ) → (k -2) +2+ ⟨0⟩ == ⟨ k ⟩
    nlemma₂ O = idp
    nlemma₂ (S k) = ap S (nlemma₂ k)

  module F = FreudenthalIso 
    (n -2) k kle' (Ptd-Susp^ n X)
    (transport (λ t → is-connected t (fst (Ptd-Susp^ n X)))
               (nlemma₁ n) (Ptd-Susp^-conn n cX))

  -- stable : Path {A = Σ _ Group}
  --   (_ , π (S k) (Ptd-Susp^ (S n) X)) 
  --   (_ , π k (Ptd-Susp^ n X))
  -- stable = group-iso 
  --   {!!} 
  --   {!!}

  -- stable : π (S k) (Susp^ (S n) A) (north^ (S n) a)
  --          == π k (Susp^ n A) (north^ n a) 
  -- stable = 
  --   Trunc ⟨ 0 ⟩ (Ω^ (S k) (Susp^ (S n) A) (north^ (S n) a))
  --     =⟨ idp ⟩
  --   Trunc ⟨ 0 ⟩ (Ω^ k (north (Susp^ n A) == north (Susp^ n A)) idp)
  --     =⟨ Trunc-Ω^-path ⟨0⟩ k _ _  ⟩
  --   Ω^ k (Trunc ((k -2) +2+ ⟨0⟩) (north (Susp^ n A) == north (Susp^ n A))) [ idp ] 
  --     =⟨ nlemma₂ k |in-ctx (λ t → Ω^ k (Trunc t (north (Susp^ n A) == north (Susp^ n A))) [ idp ]) ⟩ 
  --   Ω^ k (Trunc ⟨ k ⟩ (north (Susp^ n A) == north (Susp^ n A))) [ idp ]
  --     =⟨ Ω^-coe-path k (! F.path) [ idp ] ⟩
  --   Ω^ k (Trunc ⟨ k ⟩ (Susp^ n A)) (coe (! F.path) [ idp ])
  --     =⟨ app= (coe-! F.path) [ idp ] ∙ coe!-β F.eqv [ idp ]
  --       |in-ctx (λ w → Ω^ k (Trunc ⟨ k ⟩ (Susp^ n A)) w) ⟩
  --   Ω^ k (Trunc ⟨ k ⟩ (Susp^ n A)) [ north^ n a ] 
  --     =⟨ ! (nlemma₂ k) |in-ctx (λ t → Ω^ k (Trunc t (Susp^ n A)) [ north^ n a ]) ⟩
  --   Ω^ k (Trunc ((k -2) +2+ ⟨0⟩) (Susp^ n A)) [ north^ n a ]
  --     =⟨ ! (Trunc-Ω^-path ⟨0⟩ k _ _) ⟩
  --   Trunc ⟨ 0 ⟩ (Ω^ k (Susp^ n A) (north^ n a)) ∎
