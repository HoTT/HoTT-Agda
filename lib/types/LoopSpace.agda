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

module _ {i} where

  Ptd-Ω : Ptd i → Ptd i
  Ptd-Ω (A , a) = ∙[ (a == a) , idp ]

  Ω : Ptd i → Type i
  Ω = fst ∘ Ptd-Ω

  Ptd-Ω^ : (n : ℕ) → Ptd i → Ptd i
  Ptd-Ω^ O X = X
  Ptd-Ω^ (S n) X = Ptd-Ω (Ptd-Ω^ n X)

  Ω^ : (n : ℕ) → Ptd i → Type i
  Ω^ n X = fst (Ptd-Ω^ n X)

idp^ : ∀ {i} (n : ℕ) {X : Ptd i} → Ω^ n X
idp^ n {X} = snd (Ptd-Ω^ n X)

{- for n ≥ 1, we have a group structure on the loop space -}
module _ {i} where
  !^ : (n : ℕ) ⦃ _ : n ≠ O ⦄ {X : Ptd i} → Ω^ n X → Ω^ n X
  !^ O ⦃ posi ⦄ = ⊥-rec (posi idp)
  !^ (S n) ⦃ _ ⦄ = !

  conc^ : (n : ℕ) ⦃ _ : n ≠ O ⦄ {X : Ptd i} → Ω^ n X → Ω^ n X → Ω^ n X
  conc^ O ⦃ posi ⦄ = ⊥-rec (posi idp)
  conc^ (S n) ⦃ _ ⦄ = _∙_

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
  conc^-unit-r (S n) ⦃ _ ⦄ = ∙-unit-r 

  conc^-assoc : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p q r : Ω^ n X) 
    → conc^ n (conc^ n p q) r == conc^ n p (conc^ n q r)
  conc^-assoc O ⦃ posi ⦄ = ⊥-rec (posi idp)
  conc^-assoc (S n) ⦃ _ ⦄ = ∙-assoc

  !^-inv-l : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p : Ω^ n X)
    → conc^ n (!^ n p) p == idp^ n
  !^-inv-l O ⦃ posi ⦄ = ⊥-rec (posi idp)
  !^-inv-l (S n) ⦃ _ ⦄ = !-inv-l

  !^-inv-r : (n : ℕ) ⦃ _ : n ≠ O ⦄ (p : Ω^ n X)
    → conc^ n p (!^ n p) == idp^ n
  !^-inv-r O ⦃ posi ⦄ = ⊥-rec (posi idp)
  !^-inv-r (S n) ⦃ _ ⦄ = !-inv-r

abstract
  ap^-conc^ : ∀ {i j} (n : ℕ) ⦃ _ : n ≠ O ⦄ 
    {X : Ptd i} {Y : Ptd j} (F : fst (X ∙→ Y)) (p q : Ω^ n X)
    → fst (ap^ n F) (conc^ n p q) == conc^ n (fst (ap^ n F) p) (fst (ap^ n F) q)
  ap^-conc^ O ⦃ posi ⦄ _ _ _ = ⊥-rec (posi idp)
  ap^-conc^ (S n) ⦃ _ ⦄ {X = X} {Y = Y} F p q =
    ! gpt ∙ ap g (p ∙ q) ∙ gpt
      =⟨ ap-∙ g p q |in-ctx (λ w → ! gpt ∙ w ∙ gpt) ⟩
    ! gpt ∙ (ap g p ∙ ap g q) ∙ gpt
      =⟨ lemma (ap g p) (ap g q) gpt ⟩
    (! gpt ∙ ap g p ∙ gpt) ∙ (! gpt ∙ ap g q ∙ gpt) ∎
    where 
    g : Ω^ n X → Ω^ n Y
    g = fst (ap^ n F)

    gpt : g (idp^ n) == idp^ n
    gpt = snd (ap^ n F)

    lemma : ∀ {i} {A : Type i} {x y : A}
      → (p q : x == x) (r : x == y)
      → ! r ∙ (p ∙ q) ∙ r == (! r ∙ p ∙ r) ∙ (! r ∙ q ∙ r)
    lemma p q idp = ∙-unit-r (p ∙ q) ∙ (! (∙-unit-r p) ∙2 ! (∙-unit-r q))

{- ap^ preserves (pointed) equivalences -}
module _ {i j} {X : Ptd i} {Y : Ptd j} where

  is-equiv-ap^ : (n : ℕ) (F : fst (X ∙→ Y)) (e : is-equiv (fst F))
    → is-equiv (fst (ap^ n F))
  is-equiv-ap^ O F e = e
  is-equiv-ap^ (S n) F e = 
         pre∙-is-equiv (! (snd (ap^ n F)))
    ∘ise post∙-is-equiv (snd (ap^ n F)) 
    ∘ise snd (equiv-ap (_ , is-equiv-ap^ n F e) _ _)

  equiv-ap^ : (n : ℕ) (F : fst (X ∙→ Y)) (e : is-equiv (fst F)) 
    → Ω^ n X ≃ Ω^ n Y
  equiv-ap^ n F e = (fst (ap^ n F) , is-equiv-ap^ n F e)

Ω^-level-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (has-level ((n -2) +2+ m) (fst X) → has-level m (Ω^ n X))
Ω^-level-in m O X pX = pX
Ω^-level-in m (S n) X pX = 
  Ω^-level-in (S m) n X 
    (transport (λ k → has-level k (fst X)) (! (+2+-βr (n -2) m)) pX) 
    (idp^ n) (idp^ n)

{- Eckmann-Hilton argument -}
module _ {i} {X : Ptd i} where

  conc^2-comm : (α β : Ω^ 2 X) → conc^ 2 α β == conc^ 2 β α
  conc^2-comm α β = ! (⋆2=conc^ α β) ∙ ⋆2=⋆'2 α β ∙ ⋆'2=conc^ α β
    where
      ⋆2=conc^ : (α β : Ω^ 2 X) → α ⋆2 β == conc^ 2 α β
      ⋆2=conc^ α β = ap (λ π → π ∙ β) (∙-unit-r α)

      ⋆'2=conc^ : (α β : Ω^ 2  X) → α ⋆'2 β == conc^ 2 β α
      ⋆'2=conc^ α β = ap (λ π → β ∙ π) (∙-unit-r α)

{- Pushing truncation through loop space -}
module _ {i} where

  Trunc-Ω^ : (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
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

  Ω-Trunc-equiv : (m : ℕ₋₂) (X : Ptd i)
    → Ω (Ptd-Trunc (S m) X) ≃ Trunc m (Ω X)
  Ω-Trunc-equiv m X = Trunc=-equiv [ snd X ] [ snd X ]

{- A loop space is a pregroup, and a group if it has the right level -}
module _ {i} (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) where

  Ω^-group-structure : GroupStructure (Ω^ n X)
  Ω^-group-structure = record {
    ident = idp^ n;
    inv = !^ n;
    comp = conc^ n;
    unitl = conc^-unit-l n;
    unitr = conc^-unit-r n;
    assoc = conc^-assoc n;
    invr = !^-inv-r n;
    invl = !^-inv-l n
    }

  Ω^-group : has-level ⟨ n ⟩ (fst X) → Group i
  Ω^-group pX = group 
    (Ω^ n X)
    (Ω^-level-in ⟨0⟩ n X $
       transport (λ t → has-level t (fst X)) (+2+-comm ⟨0⟩ (n -2)) pX)
    Ω^-group-structure

{- Our definition of Ω^ builds up loops on the outside,
 - but this is equivalent to building up on the inside -}  
module _ {i} where
  Ptd-Ω^-inner-path : (n : ℕ) (X : Ptd i)
    → Ptd-Ω^ (S n) X == Ptd-Ω^ n (Ptd-Ω X)
  Ptd-Ω^-inner-path O X = idp
  Ptd-Ω^-inner-path (S n) X = ap Ptd-Ω (Ptd-Ω^-inner-path n X)

  Ptd-Ω^-inner-out : (n : ℕ) (X : Ptd i)
    → fst (Ptd-Ω^ (S n) X ∙→ Ptd-Ω^ n (Ptd-Ω X))
  Ptd-Ω^-inner-out O _ = (idf _ , idp)
  Ptd-Ω^-inner-out (S n) X = ap^ 1 (Ptd-Ω^-inner-out n X)

  Ω^-inner-out : (n : ℕ) (X : Ptd i)
    → (Ω^ (S n) X → Ω^ n (Ptd-Ω X))
  Ω^-inner-out n X = fst (Ptd-Ω^-inner-out n X)

  Ω^-inner-out-conc^ : (n : ℕ) ⦃ _ : n ≠ O ⦄ (X : Ptd i) (p q : Ω^ (S n) X)
    → Ω^-inner-out n X (conc^ (S n) p q) 
      == conc^ n (Ω^-inner-out n X p) (Ω^-inner-out n X q)
  Ω^-inner-out-conc^ O ⦃ posi ⦄ X _ _ = ⊥-rec (posi idp)
  Ω^-inner-out-conc^ (S n) ⦃ _ ⦄ X p q = 
    ap^-conc^ 1 (Ptd-Ω^-inner-out n X) p q

  Ω^-inner-is-equiv : (n : ℕ) (X : Ptd i)
    → is-equiv (fst (Ptd-Ω^-inner-out n X))
  Ω^-inner-is-equiv O X = is-eq (idf _) (idf _) (λ _ → idp) (λ _ → idp)
  Ω^-inner-is-equiv (S n) X = 
    is-equiv-ap^ 1 (Ptd-Ω^-inner-out n X) (Ω^-inner-is-equiv n X)

  Ω^-inner-equiv : (n : ℕ) (X : Ptd i) → Ω^ (S n) X ≃ Ω^ n (Ptd-Ω X)
  Ω^-inner-equiv n X = _ , Ω^-inner-is-equiv n X

