{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt
open import homotopy.Pigeonhole

module homotopy.FinSet where

-- the explicit type of finite sets, carrying the cardinality on its sleeve
FinSet-exp : Type₁
FinSet-exp = Σ ℕ λ n → BAut (Fin n)

FinSet-prop : SubtypeProp Type₀ (lsucc lzero)
FinSet-prop = (λ A → Trunc -1 (Σ ℕ λ n → Fin n == A)) , λ A → Trunc-level

-- the implicit type of finite sets, hiding the cardinality in prop. trunc.
FinSet : Type₁
FinSet = Subtype FinSet-prop

FinSet= : {A B : FinSet} → fst A == fst B → A == B
FinSet= = Subtype=-out FinSet-prop

FinFS : ℕ → FinSet
FinFS n = Fin n , [ n , idp ]

UnitFS : FinSet
UnitFS = ⊤ , [ S O , ua Fin-equiv-Coprod ∙ ap (λ C → C ⊔ ⊤) (ua Fin-equiv-Empty)
                     ∙ ua (Coprod-unit-l ⊤) ]

Fin-inj-lemma : {n m : ℕ} → n < m → Fin m == Fin n → ⊥
Fin-inj-lemma {n} {m} n<m p = i≠j (<– (ap-equiv (coe-equiv p) i j) q)
  where
    i : Fin m
    i = fst (pigeonhole n<m (coe p))

    j : Fin m
    j = fst (snd (pigeonhole n<m (coe p)))

    i≠j : i ≠ j
    i≠j = fst (snd (snd (pigeonhole n<m (coe p))))

    q : coe p i == coe p j
    q = snd (snd (snd (pigeonhole n<m (coe p))))
    
Fin-inj : (n m : ℕ) → Fin n == Fin m → n == m
Fin-inj n m p with ℕ-trichotomy n m
Fin-inj n m p | inl q = q
Fin-inj n m p | inr (inl q) = ⊥-rec (Fin-inj-lemma q (! p))
Fin-inj n m p | inr (inr q) = ⊥-rec (Fin-inj-lemma q p)

FinSet-aux-prop : (A : Type₀) → SubtypeProp ℕ (lsucc lzero)
FinSet-aux-prop A = (λ n → Trunc -1 (Fin n == A)) , (λ n → Trunc-level)
  
FinSet-aux : (A : FinSet) → Subtype (FinSet-aux-prop (fst A))
FinSet-aux (A , tz) = CE.ext tz
  where
    to : (Σ ℕ λ n → Fin n == A) → Subtype (FinSet-aux-prop A)
    to (n , p) = n , [ p ]

    to-const : (z₁ z₂ : Σ ℕ λ n → Fin n == A) → to z₁ == to z₂
    to-const (n₁ , p₁) (n₂ , p₂) = Subtype=-out (FinSet-aux-prop A) (Fin-inj n₁ n₂ (p₁ ∙ ! p₂))

    module CE =
      ConstExt ⦃ Subtype-level (FinSet-aux-prop A) ⦄ to to-const

card : FinSet → ℕ
card A = fst (FinSet-aux A)

card-conv : (A : FinSet) (n : ℕ) → Trunc -1 (Fin n == fst A) → card A == n
card-conv (A , tz) n = Trunc-rec λ p → ap card (FinSet= {A , tz} {FinFS n} (! p))

FinSet-econv : FinSet-exp ≃ FinSet
FinSet-econv = equiv to from to-from from-to
  where
    to : FinSet-exp → FinSet
    to (n , A , tp) = A , Trunc-rec (λ p → [ n , p ]) tp

    from : FinSet → FinSet-exp
    from A = card A , fst A , snd (FinSet-aux A)

    to-from : (A : FinSet) → to (from A) == A
    to-from A = pair= idp (prop-has-all-paths (snd (to (from A))) (snd A))

    from-to : (A : FinSet-exp) → from (to A) == A
    from-to A = pair= (card-conv (to A) (fst A) (snd (snd A)))
      (↓-Subtype-in (λ n → BAut-prop (Fin n)) (↓-cst-in idp))

FinSet-elim-prop : ∀ {j} {P : FinSet → Type j} (p : (A : FinSet) → has-level -1 (P A))
                   (d : (n : ℕ) → P (FinFS n)) → (A : FinSet) → P A
FinSet-elim-prop {j} {P} p d (A , tz) = Trunc-elim ⦃ λ tw → p (A , tw) ⦄
  (λ {(n , p) → transport P (FinSet= p) (d n)}) tz

finset-has-dec-eq : (A : FinSet) → has-dec-eq (fst A)
finset-has-dec-eq = FinSet-elim-prop (λ A → has-dec-eq-is-prop) λ n → Fin-has-dec-eq

-- todo: closure of FinSet under product, coproduct, exponential, etc.
