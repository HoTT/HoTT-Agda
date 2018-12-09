{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Bool
open import lib.types.Empty
open import lib.types.Paths
open import lib.types.Pi
open import lib.types.Sigma

{-
This file contains various lemmas that rely on lib.types.Paths or
functional extensionality for pointed maps.
-}

module lib.types.Pointed where

{- Sequences of pointed maps and paths between their compositions -}

infixr 80 _◃⊙∘_
data ⊙FunctionSeq {i} : Ptd i → Ptd i → Type (lsucc i) where
  ⊙idf-seq : {X : Ptd i} → ⊙FunctionSeq X X
  _◃⊙∘_ : {X Y Z : Ptd i} (g : Y ⊙→ Z) (fs : ⊙FunctionSeq X Y) → ⊙FunctionSeq X Z

infix 30 _⊙–→_
_⊙–→_ = ⊙FunctionSeq

infix 90 _◃⊙idf
_◃⊙idf : ∀ {i} {X Y : Ptd i} → (X ⊙→ Y) → X ⊙–→ Y
_◃⊙idf fs = fs ◃⊙∘ ⊙idf-seq

⊙compose : ∀ {i} {X Y : Ptd i} → (X ⊙–→ Y) → X ⊙→ Y
⊙compose ⊙idf-seq = ⊙idf _
⊙compose (g ◃⊙∘ fs) = g ⊙∘ ⊙compose fs

record _=⊙∘_ {i} {X Y : Ptd i} (fs gs : X ⊙–→ Y) : Type i where
  constructor =⊙∘-in
  field
    =⊙∘-out : ⊙compose fs == ⊙compose gs
open _=⊙∘_ public

{- Pointed maps -}

⊙→-level : ∀ {i j} (X : Ptd i) (Y : Ptd j)
  {n : ℕ₋₂}
  → has-level n (de⊙ Y)
  → has-level n (X ⊙→ Y)
⊙→-level X Y Y-level =
  Σ-level
    (Π-level (λ _ → Y-level))
    (λ f' → =-preserves-level Y-level)

⊙app= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f == g → f ⊙∼ g
⊙app= {X = X} {Y = Y} p =
  app= (fst= p) , ↓-ap-in (_== pt Y) (λ u → u (pt X)) (snd= p)

-- function extensionality for pointed maps
⊙λ= : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f ⊙∼ g → f == g
⊙λ= {g = g} (p , α) = pair= (λ= p)
  (↓-app=cst-in (↓-idf=cst-out α ∙ ap (_∙ snd g) (! (app=-β p _))))

⊙λ=' : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  (p : fst f ∼ fst g)
  (α : snd f == snd g [ (λ y → y == pt Y) ↓ p (pt X) ])
  → f == g
⊙λ=' {g = g} = curry ⊙λ=

-- associativity of pointed maps
⊙∘-assoc-pt : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {a₁ a₂ : A} (f : A → B) {b : B} (g : B → C) {c : C}
  (p : a₁ == a₂) (q : f a₂ == b) (r : g b == c)
  → ⊙∘-pt (g ∘ f) p (⊙∘-pt g q r) == ⊙∘-pt g (⊙∘-pt f p q) r
⊙∘-assoc-pt _ _ idp _ _ = idp

⊙∘-assoc : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (h : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ((h ⊙∘ g) ⊙∘ f) ⊙∼ (h ⊙∘ (g ⊙∘ f))
⊙∘-assoc (h , hpt) (g , gpt) (f , fpt) = (λ _ → idp) , ⊙∘-assoc-pt g h fpt gpt hpt

⊙∘-cst-l : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : X ⊙→ Y) → (⊙cst :> (Y ⊙→ Z)) ⊙∘ f ⊙∼ ⊙cst
⊙∘-cst-l {Z = Z} f = (λ _ → idp) , ap (_∙ idp) (ap-cst (pt Z) (snd f))

⊙∘-cst-r : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → (f : Y ⊙→ Z) → f ⊙∘ (⊙cst :> (X ⊙→ Y)) ⊙∼ ⊙cst
⊙∘-cst-r {X = X} f = (λ _ → snd f) , ↓-idf=cst-in' idp

private
  ⊙coe-pt : ∀ {i} {X Y : Ptd i} (p : X == Y)
    → coe (ap de⊙ p) (pt X) == pt Y
  ⊙coe-pt idp = idp

⊙coe : ∀ {i} {X Y : Ptd i}
  → X == Y → X ⊙→ Y
⊙coe p = coe (ap de⊙ p) , ⊙coe-pt p

⊙coe-equiv : ∀ {i} {X Y : Ptd i}
  → X == Y → X ⊙≃ Y
⊙coe-equiv p = ⊙coe p , snd (coe-equiv (ap de⊙ p))

transport-post⊙∘ : ∀ {i} {j} (X : Ptd i) {Y Z : Ptd j} (p : Y == Z)
  (f : X ⊙→ Y)
  → transport (X ⊙→_) p f == ⊙coe p ⊙∘ f
transport-post⊙∘ X p@idp f = ! (⊙λ= (⊙∘-unit-l f))

⊙coe-∙ : ∀ {i} {X Y Z : Ptd i} (p : X == Y) (q : Y == Z)
  → ⊙coe (p ∙ q) ◃⊙idf =⊙∘ ⊙coe q ◃⊙∘ ⊙coe p ◃⊙idf
⊙coe-∙ p@idp q = =⊙∘-in idp

private
  ⊙coe'-pt : ∀ {i} {X Y : Ptd i} (p : de⊙ X == de⊙ Y) (q : pt X == pt Y [ idf _ ↓ p ])
    → coe p (pt X) == pt Y
  ⊙coe'-pt p@idp q = q

⊙coe' : ∀ {i} {X Y : Ptd i} (p : de⊙ X == de⊙ Y) (q : pt X == pt Y [ idf _ ↓ p ])
  → X ⊙→ Y
⊙coe' p q = coe p , ⊙coe'-pt p q

private
  ⊙transport-pt : ∀ {i j} {A : Type i} (B : A → Ptd j) {x y : A} (p : x == y)
    → transport (de⊙ ∘ B) p (pt (B x)) == pt (B y)
  ⊙transport-pt B idp = idp

⊙transport : ∀ {i j} {A : Type i} (B : A → Ptd j) {x y : A} (p : x == y)
  → (B x ⊙→ B y)
⊙transport B p = transport (de⊙ ∘ B) p , ⊙transport-pt B p

⊙transport-∙ : ∀ {i j} {A : Type i} (B : A → Ptd j)
  {x y z : A} (p : x == y) (q : y == z)
  → ⊙transport B (p ∙ q) ◃⊙idf =⊙∘ ⊙transport B q ◃⊙∘ ⊙transport B p ◃⊙idf
⊙transport-∙ B p@idp q = =⊙∘-in idp

⊙transport-⊙coe : ∀ {i j} {A : Type i} (B : A → Ptd j) {x y : A} (p : x == y)
  → ⊙transport B p == ⊙coe (ap B p)
⊙transport-⊙coe B p@idp = idp

⊙transport-natural : ∀ {i j k} {A : Type i} {B : A → Ptd j} {C : A → Ptd k}
  {x y : A} (p : x == y)
  (h : ∀ a → B a ⊙→ C a)
  → h y ⊙∘ ⊙transport B p == ⊙transport C p ⊙∘ h x
⊙transport-natural p@idp h = ! (⊙λ= (⊙∘-unit-l (h _)))

{- This requires that B and C have the same universe level -}
⊙transport-natural-=⊙∘ : ∀ {i j} {A : Type i} {B C : A → Ptd j}
  {x y : A} (p : x == y)
  (h : ∀ a → B a ⊙→ C a)
  → h y ◃⊙∘ ⊙transport B p ◃⊙idf =⊙∘ ⊙transport C p ◃⊙∘ h x ◃⊙idf
⊙transport-natural-=⊙∘ p h = =⊙∘-in (⊙transport-natural p h)

{- Pointed equivalences -}

-- Extracting data from an pointed equivalence
module _ {i j} {X : Ptd i} {Y : Ptd j} (⊙e : X ⊙≃ Y) where

  ⊙≃-to-≃ : de⊙ X ≃ de⊙ Y
  ⊙≃-to-≃ = fst (fst ⊙e) , snd ⊙e

  ⊙–> : X ⊙→ Y
  ⊙–> = fst ⊙e

  ⊙–>-pt = snd ⊙–>

  ⊙<– : Y ⊙→ X
  ⊙<– = is-equiv.g (snd ⊙e) , lemma ⊙e where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y) → is-equiv.g (snd ⊙e) (pt Y) == pt X
    lemma ((f , idp) , f-ise) = is-equiv.g-f f-ise (pt X)

  ⊙<–-pt = snd ⊙<–

  infix 120 _⊙⁻¹
  _⊙⁻¹ : Y ⊙≃ X
  _⊙⁻¹ = ⊙<– , is-equiv-inverse (snd ⊙e)

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙<–-inv-l : (⊙e : X ⊙≃ Y) → ⊙<– ⊙e ⊙∘ ⊙–> ⊙e == ⊙idf _
  ⊙<–-inv-l ⊙e = ⊙λ= (<–-inv-l (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e)) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙<– ⊙e ⊙∘ ⊙–> ⊙e) == is-equiv.g-f (snd ⊙e) (pt X)
    lemma ((f , idp) , f-ise) = idp

  ⊙<–-inv-r : (⊙e : X ⊙≃ Y) → ⊙–> ⊙e ⊙∘ ⊙<– ⊙e == ⊙idf _
  ⊙<–-inv-r ⊙e = ⊙λ= (<–-inv-r (⊙≃-to-≃ ⊙e) , ↓-idf=cst-in' (lemma ⊙e)) where
    lemma : {Y : Ptd j} (⊙e : X ⊙≃ Y)
      → snd (⊙–> ⊙e ⊙∘ ⊙<– ⊙e) == is-equiv.f-g (snd ⊙e) (pt Y)
    lemma ((f , idp) , f-ise) = ∙-unit-r _ ∙ is-equiv.adj f-ise (pt X)

module _ {i} {X Y : Ptd i} where

  ⊙<–-inv-l-=⊙∘ : (⊙e : X ⊙≃ Y) → ⊙<– ⊙e ◃⊙∘ ⊙–> ⊙e ◃⊙idf =⊙∘ ⊙idf-seq
  ⊙<–-inv-l-=⊙∘ ⊙e = =⊙∘-in (⊙<–-inv-l ⊙e)

  ⊙<–-inv-r-=⊙∘ : (⊙e : X ⊙≃ Y) → ⊙–> ⊙e ◃⊙∘ ⊙<– ⊙e ◃⊙idf =⊙∘ ⊙idf-seq
  ⊙<–-inv-r-=⊙∘ ⊙e = =⊙∘-in (⊙<–-inv-r ⊙e)

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (⊙e : X ⊙≃ Y) where

  post⊙∘-is-equiv : is-equiv (λ (k : Z ⊙→ X) → ⊙–> ⊙e ⊙∘ k)
  post⊙∘-is-equiv = is-eq (⊙–> ⊙e ⊙∘_) (⊙<– ⊙e ⊙∘_) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : ∀ {Y} (⊙e : X ⊙≃ Y) (k : Z ⊙→ Y) → ⊙–> ⊙e ⊙∘ (⊙<– ⊙e ⊙∘ k) == k
      to-from ((f , idp) , f-ise) (k , k-pt) = ⊙λ=' (f.f-g ∘ k) (↓-idf=cst-in' $ lemma k-pt)
        where
          module f = is-equiv f-ise
          lemma : ∀ {y₀} (k-pt : y₀ == f (pt X))
            → ⊙∘-pt f (⊙∘-pt f.g k-pt (f.g-f _)) idp == f.f-g y₀ ∙' k-pt
          lemma idp = ∙-unit-r _ ∙ f.adj _

      from-to : ∀ {Y} (⊙e : X ⊙≃ Y) (k : Z ⊙→ X) → ⊙<– ⊙e ⊙∘ (⊙–> ⊙e ⊙∘ k) == k
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (f.g-f ∘ k) $ ↓-idf=cst-in' idp
        where module f = is-equiv f-ise

  post⊙∘-equiv : (Z ⊙→ X) ≃ (Z ⊙→ Y)
  post⊙∘-equiv = _ , post⊙∘-is-equiv

  pre⊙∘-is-equiv : is-equiv (λ (k : Y ⊙→ Z) → k ⊙∘ ⊙–> ⊙e)
  pre⊙∘-is-equiv = is-eq (_⊙∘ ⊙–> ⊙e) (_⊙∘ ⊙<– ⊙e) (to-from ⊙e) (from-to ⊙e) where
    abstract
      to-from : ∀ {Z} (⊙e : X ⊙≃ Y) (k : X ⊙→ Z) → (k ⊙∘ ⊙<– ⊙e) ⊙∘ ⊙–> ⊙e == k
      to-from ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.g-f) $ ↓-idf=cst-in' $ ∙-unit-r _
        where module f = is-equiv f-ise

      from-to : ∀ {Z} (⊙e : X ⊙≃ Y) (k : Y ⊙→ Z) → (k ⊙∘ ⊙–> ⊙e) ⊙∘ ⊙<– ⊙e == k
      from-to ((f , idp) , f-ise) (k , idp) = ⊙λ=' (ap k ∘ f.f-g) $ ↓-idf=cst-in' $
        ∙-unit-r _ ∙ ap-∘ k f (f.g-f (pt X)) ∙ ap (ap k) (f.adj (pt X))
        where module f = is-equiv f-ise

  pre⊙∘-equiv : (Y ⊙→ Z) ≃ (X ⊙→ Z)
  pre⊙∘-equiv = _ , pre⊙∘-is-equiv

{- Pointed maps out of bool -}

-- intuition : [f true] is fixed and the only changable part is [f false].

⊙Bool→-to-idf : ∀ {i} {X : Ptd i}
  → ⊙Bool ⊙→ X → de⊙ X
⊙Bool→-to-idf (h , _) = h false

⊙Bool→-equiv-idf : ∀ {i} (X : Ptd i)
  → (⊙Bool ⊙→ X) ≃ de⊙ X
⊙Bool→-equiv-idf {i} X = equiv ⊙Bool→-to-idf g f-g g-f
  where
  g : de⊙ X → ⊙Bool ⊙→ X
  g x = Bool-rec (pt X) x , idp

  abstract
    f-g : ∀ x → ⊙Bool→-to-idf (g x) == x
    f-g x = idp

    g-f : ∀ H → g (⊙Bool→-to-idf H) == H
    g-f (h , hpt) = pair=
      (λ= lemma)
      (↓-app=cst-in $
        idp
          =⟨ ! (!-inv-l hpt) ⟩
        ! hpt ∙ hpt
          =⟨ ! (app=-β lemma true) |in-ctx (λ w → w ∙ hpt) ⟩
        app= (λ= lemma) true ∙ hpt
          =∎)
      where lemma : ∀ b → fst (g (h false)) b == h b
            lemma true = ! hpt
            lemma false = idp

⊙Bool→-equiv-idf-nat : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y)
  → CommSquareEquiv
      (F ⊙∘_)
      (fst F)
      ⊙Bool→-to-idf
      ⊙Bool→-to-idf
⊙Bool→-equiv-idf-nat F = (comm-sqr λ _ → idp) ,
  snd (⊙Bool→-equiv-idf _) , snd (⊙Bool→-equiv-idf _)
