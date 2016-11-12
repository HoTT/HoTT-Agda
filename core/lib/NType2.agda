{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.Relation2
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.TLevel

module lib.NType2 where

module _ {i} {A : Type i} where
  abstract
    has-dec-onesided-eq-is-prop : {x : A} → is-prop (has-dec-onesided-eq x)
    has-dec-onesided-eq-is-prop {x = x} = inhab-to-prop-is-prop λ dec →
      Π-is-prop λ y → Dec-level (dec-onesided-eq-is-prop x dec y)

    has-dec-eq-is-prop : is-prop (has-dec-eq A)
    has-dec-eq-is-prop = Π-is-prop λ _ → has-dec-onesided-eq-is-prop


module _ {i j} {A : Type i} {B : A → Type j} where
  abstract
    ↓-level : {a b : A} {p : a == b} {u : B a} {v : B b} {n : ℕ₋₂}
      → has-level (S n) (B b) → has-level n (u == v [ B ↓ p ])
    ↓-level {p = idp} k = k _ _

    ↓-preserves-level : {a b : A} {p : a == b} {u : B a} {v : B b} (n : ℕ₋₂)
      → has-level n (B b) → has-level n (u == v [ B ↓ p ])
    ↓-preserves-level {p = idp} n k = =-preserves-level n k

    prop-has-all-paths-↓ : {x y : A} {p : x == y} {u : B x} {v : B y}
      → (is-prop (B y) → u == v [ B ↓ p ])
    prop-has-all-paths-↓ {p = idp} k = prop-has-all-paths k _ _

    set-↓-has-all-paths-↓ : ∀ {k} {C : Type k}
      {x y : C → A} {p : (t : C) → x t == y t} {u : (t : C) → B (x t)} {v : (t : C) → B (y t)}
      {a b : C} {q : a == b} {α : u a == v a [ B ↓ p a ]} {β : u b == v b [ B ↓ p b ]}
      → (is-set (B (y a)) → α == β [ (λ t → u t == v t [ B ↓ p t ]) ↓ q ])
    set-↓-has-all-paths-↓ {q = idp} = lemma _
      where
        lemma : {x y : A} (p : x == y) {u : B x} {v : B y} {α β : u == v [ B ↓ p ]}
          → is-set (B y) → α == β
        lemma idp k = fst (k _ _ _ _)

abstract
  -- Every map between contractible types is an equivalence
  contr-to-contr-is-equiv : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
    → (is-contr A → is-contr B → is-equiv f)
  contr-to-contr-is-equiv f cA cB =
    is-eq f (λ _ → fst cA) (λ b → ! (snd cB _) ∙ snd cB b) (snd cA)

  is-contr-is-prop : ∀ {i} {A : Type i} → is-prop (is-contr A)
  is-contr-is-prop {A = A} = all-paths-is-prop (λ x y →
    pair= (snd x (fst y))
          (↓-Π-cst-app-in (λ a → ↓-idf=cst-in' (lemma x (fst y) a (snd y a))))) where

    lemma : (x : is-contr A) (b a : A) (p : b == a)
      → snd x a == snd x b ∙' p
    lemma x b ._ idp = idp

  has-level-is-prop : ∀ {i} {n : ℕ₋₂} {A : Type i}
    → is-prop (has-level n A)
  has-level-is-prop {n = ⟨-2⟩} = is-contr-is-prop
  has-level-is-prop {n = S n} =
    Π-level (λ x → Π-level (λ y → has-level-is-prop))

  is-prop-is-prop : ∀ {i} {A : Type i} → is-prop (is-prop A)
  is-prop-is-prop = has-level-is-prop

  is-set-is-prop : ∀ {i} {A : Type i} → is-prop (is-set A)
  is-set-is-prop = has-level-is-prop

{- Subtypes. -}

module _ {i j} {A : Type i} (P : SubtypeProp A j) where
  private
    module P = SubtypeProp P

  Subtype-level : ∀ {n : ℕ₋₂}
    → has-level (S n) A
    → has-level (S n) (Subtype P)
  Subtype-level p = Σ-level p (λ x → prop-has-level-S (P.level x))

  Subtype= : (x y : Subtype P) → Type i
  Subtype= x y = fst x == fst y

  Subtype=-out : ∀ {x y : Subtype P} → Subtype= x y → x == y
  Subtype=-out p = pair= p (prop-has-all-paths-↓ (P.level _))

  Subtype=-β : {x y : Subtype P} (p : Subtype= x y)
    → fst= (Subtype=-out {x = x} {y = y} p) == p
  Subtype=-β idp = fst=-β idp _

  Subtype=-η : {x y : Subtype P} (p : x == y)
    → Subtype=-out (fst= p) == p
  Subtype=-η idp = ap (pair= idp)
    (contr-has-all-paths (P.level _ _ _) _ _)

  Subtype=-econv : (x y : Subtype P) → (Subtype= x y) ≃ (x == y)
  Subtype=-econv x y = equiv Subtype=-out fst= Subtype=-η Subtype=-β

  abstract
    Subtype-∙ : ∀ {x y z : Subtype P}
      (p : Subtype= x y) (q : Subtype= y z)
      → (Subtype=-out {x} {y} p ∙ Subtype=-out {y} {z} q)
      == Subtype=-out {x} {z} (p ∙ q)
    Subtype-∙ {x} {y} {z} p q =
      Subtype=-out p ∙ Subtype=-out q
        =⟨ Σ-∙ {p = p} {p' = q} (prop-has-all-paths-↓ (P.level (fst y))) (prop-has-all-paths-↓ (P.level (fst z))) ⟩
      pair= (p ∙ q) (prop-has-all-paths-↓ {p = p} (P.level (fst y)) ∙ᵈ prop-has-all-paths-↓ (P.level (fst z)))
        =⟨ contr-has-all-paths (↓-level (P.level (fst z))) _ (prop-has-all-paths-↓ (P.level (fst z)))
          |in-ctx pair= (p ∙ q) ⟩
      Subtype=-out (p ∙ q)
        =∎

-- Groupoids

is-gpd : {i : ULevel} → Type i → Type i
is-gpd = has-level 1

-- Type of all n-truncated types

has-level-prop : ∀ {i} → ℕ₋₂ → SubtypeProp (Type i) i
has-level-prop n = has-level n , λ _ → has-level-is-prop

_-Type_ : (n : ℕ₋₂) (i : ULevel) → Type (lsucc i)
n -Type i = Subtype (has-level-prop {i} n)

hProp : (i : ULevel) → Type (lsucc i)
hProp i = -1 -Type i

hSet : (i : ULevel) → Type (lsucc i)
hSet i = 0 -Type i

_-Type₀ : (n : ℕ₋₂) → Type₁
n -Type₀ = n -Type lzero

hProp₀ = hProp lzero
hSet₀ = hSet lzero

-- [n -Type] is an (n+1)-type

abstract
  ≃-level : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j}
    → (has-level n A → has-level n B → has-level n (A ≃ B))
  ≃-level {n = ⟨-2⟩} pA pB =
    ((cst (fst pB) , contr-to-contr-is-equiv _ pA pB)
    , (λ e → pair= (λ= (λ _ → snd pB _))
                   (from-transp is-equiv _ (fst (is-equiv-is-prop _ _)))))
  ≃-level {n = S n} pA pB =
    Σ-level (→-level pB) (λ _ → prop-has-level-S is-equiv-is-prop)

  ≃-is-set : ∀ {i j} {A : Type i} {B : Type j}
            → is-set A → is-set B → is-set (A ≃ B)
  ≃-is-set = ≃-level

  universe-=-level : ∀ {i} {n : ℕ₋₂} {A B : Type i}
    → (has-level n A → has-level n B → has-level n (A == B))
  universe-=-level pA pB = equiv-preserves-level ua-equiv (≃-level pA pB)

  universe-=-is-set : ∀ {i} {A B : Type i}
    → (is-set A → is-set B → is-set (A == B))
  universe-=-is-set = universe-=-level

module _ {i} {n} where
  private
    prop : SubtypeProp {lsucc i} (Type i) i
    prop = has-level-prop n

  nType= : (A B : n -Type i) → Type (lsucc i)
  nType= = Subtype= prop

  nType=-out : {A B : n -Type i} → nType= A B → A == B
  nType=-out = Subtype=-out prop

  abstract
    nType=-β : {A B : n -Type i} (p : nType= A B)
      → fst= (nType=-out {A = A} {B = B} p) == p
    nType=-β = Subtype=-β prop

    nType=-η : {A B : n -Type i} (p : A == B)
      → nType=-out (fst= p) == p
    nType=-η = Subtype=-η prop

    nType=-econv : (A B : n -Type i) → (nType= A B) ≃ (A == B)
    nType=-econv = Subtype=-econv prop

    nType-∙ : {A B C : n -Type i}
      (p : nType= A B) (q : nType= B C)
      → (nType=-out {A = A} p ∙ nType=-out {A = B} q)
      == nType=-out {A = A} {B = C} (p ∙ q)
    nType-∙ = Subtype-∙ prop

abstract
  _-Type-level_ : (n : ℕ₋₂) (i : ULevel)
    → has-level (S n) (n -Type i)
  (n -Type-level i) A B =
    equiv-preserves-level (nType=-econv A B)
                          (universe-=-level (snd A) (snd B))

  hProp-is-set : (i : ULevel) → is-set (hProp i)
  hProp-is-set i = -1 -Type-level i

  hSet-level : (i : ULevel) → has-level 1 (hSet i)
  hSet-level i = 0 -Type-level i

{- The following two lemmas are in NType2 instead of NType because of cyclic
   dependencies -}

module _ {i} {A : Type i} where
  abstract
    raise-level-<T : {m n : ℕ₋₂} → (m <T n) → has-level m A → has-level n A
    raise-level-<T ltS = raise-level _
    raise-level-<T (ltSR lt) = raise-level _ ∘ raise-level-<T lt

    raise-level-≤T : {m n : ℕ₋₂} → (m ≤T n) → has-level m A → has-level n A
    raise-level-≤T (inl p) = transport (λ t → has-level t A) p
    raise-level-≤T (inr lt) = raise-level-<T lt
