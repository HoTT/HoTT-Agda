{-# OPTIONS --without-K --rewriting #-}

open import HoTT

-- This file contains a helper module for FinSet,
-- proving the finite pigeonhole principle
module homotopy.Pigeonhole where

{-
  loosely based on code by copumpkin and xplat via byorgey
-}

incl : ∀ {m n} (m<n : m < n) → Fin m → Fin n
incl m<n (k , k<m) = k , <-trans k<m m<n

incl-ne : ∀ {n} (i : Fin n) → ¬ (incl ltS i == n , ltS)
incl-ne {n} (k , k<n) p = <-to-≠ k<n (ap fst p)

Dec-Σ-Fin : ∀ {ℓ} {n} (P : Fin n → Type ℓ) (dec-P : (i : Fin n) → Dec (P i))
             → Dec (Σ (Fin n) λ i → P i)
Dec-Σ-Fin {ℓ} {O} P dec-P = inr λ z → –> Fin-equiv-Empty (fst z)
Dec-Σ-Fin {ℓ} {S n} P dec-P with Dec-Σ-Fin {ℓ} {n} (P ∘ (incl ltS)) (dec-P ∘ (incl ltS))
Dec-Σ-Fin {ℓ} {S n} P dec-P | inl z = inl (incl ltS (fst z) , snd z)
Dec-Σ-Fin {ℓ} {S n} P dec-P | inr ¬z with dec-P (n , ltS)
Dec-Σ-Fin {ℓ} {S n} P dec-P | inr ¬z | (inl p)  = inl ((n , ltS) , p)
Dec-Σ-Fin {ℓ} {S n} P dec-P | inr ¬z | (inr ¬p) = inr ¬w
  where
    ¬w : Σ (Fin (S n)) P → ⊥
    ¬w ((_ , ltS) , p) = ¬p p
    ¬w ((k , ltSR k<n) , p) = ¬z ((k , k<n) , p)

<-trans-S : {m n k : ℕ} → m < n → n < (S k) → m < k
<-trans-S m<n ltS = m<n
<-trans-S m<n (ltSR n<k) = <-trans m<n n<k

ℕ-dichotomy : {m n : ℕ} → m ≠ n → (m < n) ⊔ (n < m)
ℕ-dichotomy {m} {n} m≠n with ℕ-trichotomy m n
ℕ-dichotomy {m} {n} m≠n | inl p = ⊥-rec (m≠n p)
ℕ-dichotomy {m} {n} m≠n | inr x = x

Fin-fst-= : ∀ {n} {i j : Fin n} → fst i == fst j → i == j
Fin-fst-= {n} {i , i<n} {j , j<n} = Subtype=-out (Fin-prop n)

punchout : ∀ {n} (i j : Fin (S n)) → i ≠ j → Fin n
punchout {n} (i , i<Sn) (j , j<Sn) i≠j with ℕ-dichotomy (i≠j ∘ Fin-fst-=)
punchout {n} (i , i<Sn) (.(S i) , Si<Sn) i≠j | inl ltS = i , <-trans-S ltS Si<Sn
punchout {n} (i , i<Sn) (S j , Sj<Sn) i≠j | inl (ltSR i<j) = j , <-cancel-S Sj<Sn
punchout {n} (i , i<Sn) (j , j<Sn) i≠j | inr j<i = j , <-trans-S j<i i<Sn

punchout-inj : ∀ {n} (i j k : Fin (S n)) (i≠j : i ≠ j) (i≠k : i ≠ k)
               → punchout i j i≠j == punchout i k i≠k → j == k
punchout-inj {n} (i , i<Sn) (j , j<Sn) (k , k<Sn) i≠j i≠k q with ℕ-dichotomy (i≠j ∘ Fin-fst-=)
punchout-inj {n} (i , i<Sn) (.(S i) , Si<Sn) (k , k<Sn) i≠j i≠k q | inl ltS with ℕ-dichotomy (i≠k ∘ Fin-fst-=)
punchout-inj {n} (i , i<Sn) (.(S i) , Si<Sn) (.(S i) , _) i≠j i≠k q | inl ltS | inl ltS = Fin-fst-= idp
punchout-inj {n} (i , i<Sn) (.(S i) , Si<Sn) (S k , Sk<Sn) i≠j i≠k q | inl ltS | inl (ltSR i<k) = ⊥-rec (<-to-≠ i<k (ap fst q))
punchout-inj {n} (i , i<Sn) (.(S i) , Si<Sn) (k , k<Sn) i≠j i≠k q | inl ltS | inr k<i = ⊥-rec (i≠k (Fin-fst-= (ap fst q)))
punchout-inj {n} (i , i<Sn) (S j , Sj<Sn) (k , k<Sn) i≠j i≠k q | inl (ltSR i<j) with ℕ-dichotomy (i≠k ∘ Fin-fst-=)
punchout-inj {n} (i , i<Sn) (S j , Sj<Sn) (.(S i) , Si<Sn) i≠j i≠k q | inl (ltSR i<j) | inl ltS = ⊥-rec (<-to-≠ i<j (! (ap fst q)))
punchout-inj {n} (i , i<Sn) (S j , Sj<Sn) (S k , Sk<Sn) i≠j i≠k q | inl (ltSR i<j) | inl (ltSR i<k) = Fin-fst-= (ap S (ap fst q))
punchout-inj {n} (i , i<Sn) (S j , Sj<Sn) (k , k<Sn) i≠j i≠k q | inl (ltSR i<j) | inr k<i = ⊥-rec (<-to-≠ (<-trans k<i i<j) (! (ap fst q)))
punchout-inj {n} (i , i<Sn) (j , j<Sn) (k , k<Sn) i≠j i≠k q | inr j<i with ℕ-dichotomy (i≠k ∘ Fin-fst-=)
punchout-inj {n} (i , i<Sn) (j , j<Sn) (.(S i) , Si<Sn) i≠j i≠k q | inr j<i | (inl ltS) = ⊥-rec (i≠j (Fin-fst-= (! (ap fst q))))
punchout-inj {n} (i , i<Sn) (j , j<Sn) (S k , Sk<Sn) i≠j i≠k q | inr j<i | (inl (ltSR i<k)) = ⊥-rec (<-to-≠ (<-trans j<i i<k) (ap fst q))
punchout-inj {n} (i , i<Sn) (j , j<Sn) (k , k<Sn) i≠j i≠k q | inr j<i | (inr k<i) = Fin-fst-= (ap fst q)

pigeonhole-special : ∀ {n} (f : Fin (S n) → Fin n)
                     → Σ (Fin (S n)) λ i → Σ (Fin (S n)) λ j → (i ≠ j) × (f i == f j)
pigeonhole-special {O} f = ⊥-rec (–> Fin-equiv-Empty (f (O , ltS)))
pigeonhole-special {S n} f with Dec-Σ-Fin (λ i → f (incl ltS i) == f (S n , ltS))
                                          (λ i → Fin-has-dec-eq (f (incl ltS i)) (f (S n , ltS)))
pigeonhole-special {S n} f | inl (i , p) = incl ltS i , (S n , ltS) , incl-ne i , p
pigeonhole-special {S n} f | inr h = incl ltS i , incl ltS j , (λ q → i≠j (Fin-fst-= (ap fst q))) ,
     punchout-inj (f (S n , ltS)) (f (incl ltS i)) (f (incl ltS j))
     (λ q → h (i , Fin-fst-= (! (ap fst q))))
     (λ q → h (j , Fin-fst-= (! (ap fst q))))
     (Fin-fst-= (ap fst p))
  where
    g : Fin (S n) → Fin n
    g k = punchout (f (S n , ltS)) (f (incl ltS k)) λ p → h (k , Fin-fst-= (! (ap fst p)))

    i : Fin (S n)
    i = fst (pigeonhole-special g)

    j : Fin (S n)
    j = fst (snd (pigeonhole-special g))

    i≠j : i ≠ j
    i≠j = fst (snd (snd (pigeonhole-special g)))

    p : g i == g j
    p = snd (snd (snd (pigeonhole-special g)))

pigeonhole : ∀ {m n} (m<n : m < n) (f : Fin n → Fin m)
             → Σ (Fin n) λ i → Σ (Fin n) λ j → (i ≠ j) × (f i == f j)
pigeonhole {m} {.(S m)} ltS f = pigeonhole-special f
pigeonhole {m} {(S n)} (ltSR p) f = i , j , ¬q , Subtype=-out (Fin-prop m) (ap fst r)
  where
    g : Fin (S n) → Fin n
    g k = fst (f k) , <-trans (snd (f k)) p

    i : Fin (S n)
    i = fst (pigeonhole-special g)

    j : Fin (S n)
    j = fst (snd (pigeonhole-special g))

    ¬q : i == j → ⊥
    ¬q = fst (snd (snd (pigeonhole-special g)))

    r : g i == g j
    r = snd (snd (snd (pigeonhole-special g)))
