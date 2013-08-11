{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Empty
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.Pointed
open import lib.types.Group

module lib.types.LoopSpace where

Ptd-Ω^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Ω^ O X = X
Ptd-Ω^ (S n) X = Ptd-Ω (Ptd-Ω^ n X)

Ω^ : ∀ {i} (n : ℕ) → Ptd i → Type i
Ω^ n X = fst (Ptd-Ω^ n X)

idp^ : ∀ {i} (n : ℕ) {X : Ptd i} → Ω^ n X
idp^ n {X} = snd (Ptd-Ω^ n X)

!^ : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ {X : Ptd i} → Ω^ n X → Ω^ n X
!^ O ⦃ posi ⦄ = ⊥-rec (posi idp)
!^ (S n) = !

conc^ : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ {X : Ptd i} → Ω^ n X → Ω^ n X → Ω^ n X
conc^ O ⦃ posi ⦄ = ⊥-rec (posi idp)
conc^ (S n) = _∙_

ap^ : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → fst (X ∙→ Y) → fst (Ptd-Ω^ n X ∙→ Ptd-Ω^ n Y)
ap^ O F = F
ap^ (S n) F = 
  let (g , gpt) = ap^ n F
  in (λ p → ! gpt ∙ ap g p ∙ gpt), !-inv-l gpt

module _ {i} {X : Ptd i} where 

  {- Prove these as lemmas now 
   - so we don't have to deal with the n = O case later -}

  conc^-unit-l : (n : ℕ) ⦃ _ : n ≠ O ⦄ (q : Ω^ n X) 
    → (conc^ n (idp^ n) q) == q
  conc^-unit-l O ⦃ posi ⦄ _ = ⊥-rec (posi idp)
  conc^-unit-l (S n) _ = idp

  conc^-unit-r : (n : ℕ) ⦃ _ : n ≠ O ⦄ (q : Ω^ n X) 
    → (conc^ n q (idp^ n)) == q
  conc^-unit-r O ⦃ posi ⦄ = ⊥-rec (posi idp)
  conc^-unit-r (S n) = ∙-unit-r 

  conc^-assoc : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p q r : Ω^ n X) 
    → conc^ n (conc^ n p q) r == conc^ n p (conc^ n q r)
  conc^-assoc O ⦃ posi ⦄ = ⊥-rec (posi idp)
  conc^-assoc (S n) = ∙-assoc

  !^-inv-l : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p : Ω^ n X)
    → conc^ n (!^ n p) p == idp^ n
  !^-inv-l O ⦃ posi ⦄ = ⊥-rec (posi idp)
  !^-inv-l (S n) = !-inv-l

  !^-inv-r : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p : Ω^ n X)
    → conc^ n p (!^ n p) == idp^ n
  !^-inv-r O ⦃ posi ⦄ = ⊥-rec (posi idp)
  !^-inv-r (S n) = !-inv-r

ap^-conc^ : ∀ {i j} (n : ℕ) ⦃ _ : n ≠ O ⦄ {X : Ptd i} {Y : Ptd j}
  → {p q : Ω^ n X} {F : fst (X ∙→ Y)}
  → fst (ap^ n F) (conc^ n p q) == conc^ n (fst (ap^ n F) p) (fst (ap^ n F) q)
ap^-conc^ O ⦃ posi ⦄ {p = _} {q = _} {F = _} = ⊥-rec (posi idp)
ap^-conc^ (S n) {p = p} {q = q} {F = F}  = 
  ! gpt ∙ ap g (p ∙ q) ∙ gpt
    =⟨ ap-∙ g p q |in-ctx (λ w → ! gpt ∙ w ∙ gpt) ⟩
  ! gpt ∙ (ap g p ∙ ap g q) ∙ gpt
    =⟨ lemma (ap g p) (ap g q) gpt ⟩
  (! gpt ∙ ap g p ∙ gpt) ∙ (! gpt ∙ ap g q ∙ gpt) ∎
  where 
  g = fst (ap^ n F)
  gpt = snd (ap^ n F)

  lemma : ∀ {i} {A : Type i} {x y : A}
    → (p q : x == x) (r : x == y)
    → ! r ∙ (p ∙ q) ∙ r == (! r ∙ p ∙ r) ∙ (! r ∙ q ∙ r)
  lemma p q idp = ∙-unit-r (p ∙ q) ∙ (! (∙-unit-r p) ∙2 ! (∙-unit-r q))

{- ap^ preserves (pointed) equivalences -}
is-equiv-ap^ : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} 
  {F : fst (X ∙→ Y)} (e : is-equiv (fst F))
  → is-equiv (fst (ap^ n F))
is-equiv-ap^ O e = e
is-equiv-ap^ (S n) {F = F} e = 
       pre∙-is-equiv (! (snd (ap^ n F)))
  ∘ise post∙-is-equiv (snd (ap^ n F)) 
  ∘ise snd (equiv-ap (_ , is-equiv-ap^ n e) _ _)

Ω^-level-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (has-level ((n -2) +2+ m) (fst X) → has-level m (Ω^ n X))
Ω^-level-in m O X pX = pX
Ω^-level-in m (S n) X pX = 
  Ω^-level-in (S m) n X 
    (transport (λ k → has-level k (fst X)) (! (+2+-βr (n -2) m)) pX) 
    (idp^ n) (idp^ n)

Trunc-Ω^ : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → Ptd-Trunc m (Ptd-Ω^ n X) == Ptd-Ω^ n (Ptd-Trunc ((n -2) +2+ m) X)
Trunc-Ω^ m O X = idp
Trunc-Ω^ m (S n) X = 
  Ptd-Trunc m (Ptd-Ω^ (S n) X)
    =⟨ ! (pair= (Trunc=-path [ _ ] [ _ ]) (↓-idf-ua-in _ idp)) ⟩
  Ptd-Ω (Ptd-Trunc (S m) (Ptd-Ω^ n X))
    =⟨ ap Ptd-Ω (Trunc-Ω^ (S m) n X) ⟩
  Ptd-Ω^ (S n) (Ptd-Trunc ((n -2) +2+ S m) X) 
    =⟨ +2+-βr (n -2) m |in-ctx (λ k → Ptd-Ω^ (S n) (Ptd-Trunc k X)) ⟩
  Ptd-Ω^ (S n) (Ptd-Trunc (S (n -2) +2+ m) X) ∎

Ω^-group : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i)
  → has-level ⟨ n ⟩ (fst X) → Group (Ω^ n X)
Ω^-group n X pX = record {
  El-level = Ω^-level-in ⟨0⟩ n X $
    transport (λ t → has-level t (fst X)) (+2+-comm ⟨0⟩ (n -2)) pX;
  ident = idp^ n;
  inv = !^ n;
  comp = conc^ n;
  unitl = conc^-unit-l n;
  unitr = conc^-unit-r n;
  assoc = conc^-assoc n;
  invr = !^-inv-r n;
  invl = !^-inv-l n
  }

{- Using instance arguments makes this not always definitional -}
Ω^-group-ident : ∀ {i} {n : ℕ} ⦃ _ : n ≠ O ⦄ {X : Ptd i} 
  {pX : has-level ⟨ n ⟩ (fst X)}
  → Group.ident (Ω^-group n X pX) == idp^ n
Ω^-group-ident {i} {O} ⦃ posi ⦄ = ⊥-rec (posi idp)
Ω^-group-ident {i} {S n} = idp

-- Ω^-group-conc : ∀ {i} {n : ℕ} ⦃ _ : n ≠ O ⦄ {X : Ptd i}
--   {pX : has-level ⟨ n ⟩ (fst X)}
--   → Group.
  
π : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) → Group (Trunc ⟨0⟩ (Ω^ n X))
π O ⦃ posi ⦄ _ = ⊥-rec (posi idp)
π (S n) ⦃ posi ⦄ X = record {
  El-level = Trunc-level;
  ident = [ idp^ (S n) ];
  inv = Trunc-fmap (!^ (S n) ⦃ posi ⦄);
  comp = Trunc-rec (Π-level (λ _ → Trunc-level)) 
                   (Trunc-fmap ∘ conc^ (S n) ⦃ posi ⦄);

  unitl = Trunc-elim 
    (λ _ → =-preserves-level _ Trunc-level) 
    (λ _ → idp);

  unitr = Trunc-elim 
    (λ _ → =-preserves-level _ Trunc-level)
    (λ a → ap [_] (∙-unit-r a));

  assoc = Trunc-elim 
    (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)))
    (λ a → Trunc-elim
      (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
      (λ b → Trunc-elim 
         (λ _ → =-preserves-level _ Trunc-level) 
         (λ c → ap [_] (∙-assoc a b c))));

  invr = Trunc-elim
    (λ _ → =-preserves-level _ Trunc-level)
    (λ a → ap [_] (!-inv-r a));

  invl = Trunc-elim
    (λ _ → =-preserves-level _ Trunc-level)
    (λ a → ap [_] (!-inv-l a))

  }

postulate
  π-Trunc-≤T : ∀ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (m : ℕ₋₂) (X : Ptd i)
    → (⟨ n ⟩ ≤T m)
    → Path {A = Σ (Type i) Group} (_ , π n (Ptd-Trunc m X)) (_ , π n X)

-- π-Trunc-≤T : ∀ {i} (n : ℕ) (m : ℕ₋₂) (A : Type i) (a : A) → (⟨ n ⟩ ≤T m) 
--   → π n (Trunc m A) [ a ] == π n A a
-- π-Trunc-≤T n m A a lte = 
--   π n (Trunc m A) [ a ]
--     =⟨ ap (λ t → π n (Trunc t A) [ a ]) 
--           (! (snd w) ∙ +2+-comm (fst w) ⟨ n ⟩ ∙ nlemma n (fst w)) ⟩
--   π n (Trunc ((n -2) +2+ (S (S (fst w)))) A) [ a ]
--     =⟨ ap (Trunc ⟨0⟩) (! (Trunc-Ω^-path (S (S (fst w))) n A a)) ⟩
--   Trunc ⟨0⟩ (Trunc (S (S (fst w))) (Ω^ n A a))
--     =⟨ ua $ fuse-Trunc _ ⟨0⟩ (S (S (fst w))) ⟩
--   Trunc ⟨0⟩ (Ω^ n A a) ∎
--   where
--     w : Σ ℕ₋₂ (λ k → k +2+ ⟨ n ⟩ == m)
--     w = ≤T-witness lte

--     nlemma : (n : ℕ) (k : ℕ₋₂) → ⟨ n ⟩ +2+ k == (n -2) +2+ (S (S k))
--     nlemma O k = idp
--     nlemma (S n) k = ap S (nlemma n k)

