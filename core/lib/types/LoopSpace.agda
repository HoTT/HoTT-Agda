{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Empty
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.PointedSigma
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Truncation

module lib.types.LoopSpace where

{- loop space -}

module _ {i} where

  ⊙Ω : Ptd i → Ptd i
  ⊙Ω (A , a) = ⊙[ (a == a) , idp ]

  Ω : Ptd i → Type i
  Ω = fst ∘ ⊙Ω

module _ {i} {X : Ptd i} where

  Ω-! : Ω X → Ω X
  Ω-! = !

  Ω-∙ : Ω X → Ω X → Ω X
  Ω-∙ = _∙_

{- pointed versions of functions on paths -}

⊙Ω-∙ : ∀ {i} {X : Ptd i} → ⊙Ω X ⊙× ⊙Ω X ⊙→ ⊙Ω X
⊙Ω-∙ = (uncurry Ω-∙ , idp)

⊙Ω-fmap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Ω X ⊙→ ⊙Ω Y
⊙Ω-fmap (f , idp) = ap f , idp

Ω-fmap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → (Ω X → Ω Y)
Ω-fmap F = fst (⊙Ω-fmap F)

Ω-isemap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  (F : X ⊙→ Y) → is-equiv (fst F) → is-equiv (Ω-fmap F)
Ω-isemap (f , idp) e = ap-is-equiv e _ _

Ω-emap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → (X ⊙≃ Y) → (Ω X ≃ Ω Y)
Ω-emap (F , F-is-equiv) = Ω-fmap F , Ω-isemap F F-is-equiv

⊙Ω-emap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → (X ⊙≃ Y) → (⊙Ω X ⊙≃ ⊙Ω Y)
⊙Ω-emap (F , F-is-equiv) = ⊙Ω-fmap F , Ω-isemap F F-is-equiv

⊙Ω-fmap2 : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → X ⊙× Y ⊙→ Z → ⊙Ω X ⊙× ⊙Ω Y ⊙→ ⊙Ω Z
⊙Ω-fmap2 (f , idp) = (λ{(p , q) → ap2 (curry f) p q}) , idp

⊙Ω-fmap-∘ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Ω-fmap (g ⊙∘ f) == ⊙Ω-fmap g ⊙∘ ⊙Ω-fmap f
⊙Ω-fmap-∘ (g , idp) (f , idp) = ⊙λ= (λ p → ap-∘ g f p) idp

⊙Ω-fmap-idf : ∀ {i} {X : Ptd i} → ⊙Ω-fmap (⊙idf X) == ⊙idf _
⊙Ω-fmap-idf = ⊙λ= ap-idf idp

⊙Ω-fmap2-fst : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Ω-fmap2 {X = X} {Y = Y} ⊙fst == ⊙fst
⊙Ω-fmap2-fst = ⊙λ= (uncurry ap2-fst) idp

⊙Ω-fmap2-snd : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Ω-fmap2 {X = X} {Y = Y} ⊙snd == ⊙snd
⊙Ω-fmap2-snd = ⊙λ= (uncurry ap2-snd) idp

⊙Ω-fmap-fmap2 : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : Z ⊙→ W) (F : X ⊙× Y ⊙→ Z)
  → ⊙Ω-fmap G ⊙∘ ⊙Ω-fmap2 F == ⊙Ω-fmap2 (G ⊙∘ F)
⊙Ω-fmap-fmap2 (g , idp) (f , idp) =
  ⊙λ= (uncurry (ap-ap2 g (curry f))) idp

⊙Ω-fmap2-fmap : ∀ {i j k l m}
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : (U ⊙× V) ⊙→ Z) (F₁ : X ⊙→ U) (F₂ : Y ⊙→ V)
  → ⊙Ω-fmap2 G ⊙∘ ⊙×-fmap (⊙Ω-fmap F₁) (⊙Ω-fmap F₂) == ⊙Ω-fmap2 (G ⊙∘ ⊙×-fmap F₁ F₂)
⊙Ω-fmap2-fmap (g , idp) (f₁ , idp) (f₂ , idp) =
  ⊙λ= (λ {(p , q) → ap2-ap-l (curry g) f₁ p (ap f₂ q)
                  ∙ ap2-ap-r (λ x v → g (f₁ x , v)) f₂ p q})
      idp

⊙Ω-fmap2-diag : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙× X ⊙→ Y)
  → ⊙Ω-fmap2 F ⊙∘ ⊙diag == ⊙Ω-fmap (F ⊙∘ ⊙diag)
⊙Ω-fmap2-diag (f , idp) = ⊙λ= (ap2-diag (curry f)) idp

{- iterated loop spaces -}

module _ {i} where

  ⊙Ω^ : (n : ℕ) → Ptd i → Ptd i
  ⊙Ω^ O X = X
  ⊙Ω^ (S n) X = ⊙Ω (⊙Ω^ n X)

  Ω^ : (n : ℕ) → Ptd i → Type i
  Ω^ n X = fst (⊙Ω^ n X)

{- for n ≥ 1, we have a group structure on the loop space -}
module _ {i} (n : ℕ) {X : Ptd i} where

  Ω^S-! : Ω^ (S n) X → Ω^ (S n) X
  Ω^S-! = Ω-!

  Ω^S-∙ : Ω^ (S n) X → Ω^ (S n) X → Ω^ (S n) X
  Ω^S-∙ = Ω-∙

idp^ : ∀ {i} (n : ℕ) {X : Ptd i} → Ω^ n X
idp^ n {X} = snd (⊙Ω^ n X)

{- [⊙Ω^-fmap] and [⊙Ω^-fmap2] for higher loop spaces -}

⊙Ω^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Ω^ n X ⊙→ ⊙Ω^ n Y
⊙Ω^-fmap O F = F
⊙Ω^-fmap (S n) F = ⊙Ω-fmap (⊙Ω^-fmap n F)

Ω^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → (fst (⊙Ω^ n X) → fst (⊙Ω^ n Y))
Ω^-fmap n F = fst (⊙Ω^-fmap n F)

⊙Ω^-fmap2 : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → ((X ⊙× Y) ⊙→ Z)
  → ((⊙Ω^ n X ⊙× ⊙Ω^ n Y) ⊙→ ⊙Ω^ n Z)
⊙Ω^-fmap2 O F = F
⊙Ω^-fmap2 (S n) F = ⊙Ω-fmap2 (⊙Ω^-fmap2 n F)

Ω^-fmap2 : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → ((X ⊙× Y) ⊙→ Z)
  → ((Ω^ n X) × (Ω^ n Y) → Ω^ n Z)
Ω^-fmap2 n F = fst (⊙Ω^-fmap2 n F)

⊙Ω^-fmap-idf : ∀ {i} (n : ℕ) {X : Ptd i} → ⊙Ω^-fmap n (⊙idf X) == ⊙idf _
⊙Ω^-fmap-idf O = idp
⊙Ω^-fmap-idf (S n) = ap ⊙Ω-fmap (⊙Ω^-fmap-idf n) ∙ ⊙Ω-fmap-idf

Ω^-fmap-idf : ∀ {i} (n : ℕ) {X : Ptd i} → Ω^-fmap n (⊙idf X) == idf _
Ω^-fmap-idf n = fst= $ ⊙Ω^-fmap-idf n

⊙Ω^-fmap-fmap2 : ∀ {i j k l} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : Z ⊙→ W) (F : (X ⊙× Y) ⊙→ Z)
  → ⊙Ω^-fmap n G ⊙∘ ⊙Ω^-fmap2 n F == ⊙Ω^-fmap2 n (G ⊙∘ F)
⊙Ω^-fmap-fmap2 O G F = idp
⊙Ω^-fmap-fmap2 (S n) G F = ⊙Ω-fmap-fmap2 (⊙Ω^-fmap n G) (⊙Ω^-fmap2 n F) ∙ ap ⊙Ω-fmap2 (⊙Ω^-fmap-fmap2 n G F)

Ω^-fmap-fmap2 : ∀ {i j k l} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : Z ⊙→ W) (F : (X ⊙× Y) ⊙→ Z)
  → Ω^-fmap n G ∘ Ω^-fmap2 n F == Ω^-fmap2 n (G ⊙∘ F)
Ω^-fmap-fmap2 n G F = fst= $ ⊙Ω^-fmap-fmap2 n G F

⊙Ω^-fmap2-fst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙Ω^-fmap2 n {X} {Y} ⊙fst == ⊙fst
⊙Ω^-fmap2-fst O = idp
⊙Ω^-fmap2-fst (S n) = ap ⊙Ω-fmap2 (⊙Ω^-fmap2-fst n) ∙ ⊙Ω-fmap2-fst

Ω^-fmap2-fst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → Ω^-fmap2 n {X} {Y} ⊙fst == fst
Ω^-fmap2-fst n = fst= $ ⊙Ω^-fmap2-fst n

⊙Ω^-fmap2-snd : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙Ω^-fmap2 n {X} {Y} ⊙snd == ⊙snd
⊙Ω^-fmap2-snd O = idp
⊙Ω^-fmap2-snd (S n) = ap ⊙Ω-fmap2 (⊙Ω^-fmap2-snd n) ∙ ⊙Ω-fmap2-snd

Ω^-fmap2-snd : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → Ω^-fmap2 n {X} {Y} ⊙snd == snd
Ω^-fmap2-snd n = fst= $ ⊙Ω^-fmap2-snd n

⊙Ω^-fmap2-fmap : ∀ {i j k l m} (n : ℕ)
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : (U ⊙× V) ⊙→ Z) (F₁ : X ⊙→ U) (F₂ : Y ⊙→ V)
  → ⊙Ω^-fmap2 n G ⊙∘ ⊙×-fmap (⊙Ω^-fmap n F₁) (⊙Ω^-fmap n F₂) == ⊙Ω^-fmap2 n (G ⊙∘ ⊙×-fmap F₁ F₂)
⊙Ω^-fmap2-fmap O G F₁ F₂ = idp
⊙Ω^-fmap2-fmap (S n) G F₁ F₂ =
  ⊙Ω-fmap2-fmap (⊙Ω^-fmap2 n G) (⊙Ω^-fmap n F₁) (⊙Ω^-fmap n F₂) ∙ ap ⊙Ω-fmap2 (⊙Ω^-fmap2-fmap n G F₁ F₂)

Ω^-fmap2-fmap : ∀ {i j k l m} (n : ℕ)
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : (U ⊙× V) ⊙→ Z) (F₁ : X ⊙→ U) (F₂ : Y ⊙→ V)
  → Ω^-fmap2 n G ∘ ×-fmap (Ω^-fmap n F₁) (Ω^-fmap n F₂) == Ω^-fmap2 n (G ⊙∘ ⊙×-fmap F₁ F₂)
Ω^-fmap2-fmap n G F₁ F₂ = fst= $ ⊙Ω^-fmap2-fmap n G F₁ F₂

⊙Ω^-fmap2-diag : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} (F : X ⊙× X ⊙→ Y)
  → ⊙Ω^-fmap2 n F ⊙∘ ⊙diag == ⊙Ω^-fmap n (F ⊙∘ ⊙diag)
⊙Ω^-fmap2-diag O F = idp
⊙Ω^-fmap2-diag (S n) F = ⊙Ω-fmap2-diag (⊙Ω^-fmap2 n F) ∙ ap ⊙Ω-fmap (⊙Ω^-fmap2-diag n F)

Ω^-fmap2-diag : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} (F : X ⊙× X ⊙→ Y)
  → Ω^-fmap2 n F ∘ diag == Ω^-fmap n (F ⊙∘ ⊙diag)
Ω^-fmap2-diag n F = fst= $ ⊙Ω^-fmap2-diag n F

module _ {i} {X : Ptd i} (n : ℕ) where

  {- Prove these as lemmas now
   - so we don't have to deal with the n = O case later -}

  Ω^S-∙-unit-l : (q : Ω^ (S n) X)
    → (Ω^S-∙ n (idp^ (S n)) q) == q
  Ω^S-∙-unit-l _ = idp

  Ω^S-∙-unit-r : (q : Ω^ (S n) X)
    → (Ω^S-∙ n q (idp^ (S n))) == q
  Ω^S-∙-unit-r = ∙-unit-r

  Ω^S-∙-assoc : (p q r : Ω^ (S n) X)
    → Ω^S-∙ n (Ω^S-∙ n p q) r == Ω^S-∙ n p (Ω^S-∙ n q r)
  Ω^S-∙-assoc = ∙-assoc

  Ω^S-!-inv-l : (p : Ω^ (S n) X)
    → Ω^S-∙ n (Ω^S-! n p) p == idp^ (S n)
  Ω^S-!-inv-l = !-inv-l

  Ω^S-!-inv-r : (p : Ω^ (S n) X)
    → Ω^S-∙ n p (Ω^S-! n p) == idp^ (S n)
  Ω^S-!-inv-r = !-inv-r

module _ where
  Ω-fmap-∙ : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) (p q : Ω X)
    → Ω-fmap F (p ∙ q) == Ω-fmap F p ∙ Ω-fmap F q
  Ω-fmap-∙ (f , idp) p q = ap-∙ f p q

  Ω^S-fmap-∙ : ∀ {i j} (n : ℕ)
    {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) (p q : Ω^ (S n) X)
    → Ω^-fmap (S n) F (Ω^S-∙ n p q)
      == Ω^S-∙ n (Ω^-fmap (S n) F p) (Ω^-fmap (S n) F q)
  Ω^S-fmap-∙ n F = Ω-fmap-∙ (⊙Ω^-fmap n F)

{- [Ω^] preserves (pointed) equivalences -}
module _ {i j} {X : Ptd i} {Y : Ptd j} where

  Ω^-isemap : (n : ℕ) (F : X ⊙→ Y) (e : is-equiv (fst F))
    → is-equiv (Ω^-fmap n F)
  Ω^-isemap O F e = e
  Ω^-isemap (S n) F e = Ω-isemap (⊙Ω^-fmap n F) (Ω^-isemap n F e)

  ⊙Ω^-isemap = Ω^-isemap

  Ω^-emap : (n : ℕ) → X ⊙≃ Y → Ω^ n X ≃ Ω^ n Y
  Ω^-emap n (F , e) = Ω^-fmap n F , Ω^-isemap n F e

  ⊙Ω^-emap : (n : ℕ) → X ⊙≃ Y → ⊙Ω^ n X ⊙≃ ⊙Ω^ n Y
  ⊙Ω^-emap n (F , e) = ⊙Ω^-fmap n F , ⊙Ω^-isemap n F e

Ω^-level : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (has-level (⟨ n ⟩₋₂ +2+ m) (fst X) → has-level m (Ω^ n X))
Ω^-level m O X pX = pX
Ω^-level m (S n) X pX =
  Ω^-level (S m) n X
    (transport (λ k → has-level k (fst X)) (! (+2+-βr ⟨ n ⟩₋₂ m)) pX)
    (idp^ n) (idp^ n)

Ω^-conn : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (is-connected (⟨ n ⟩₋₂ +2+ m) (fst X)) → is-connected m (Ω^ n X)
Ω^-conn m O X pX = pX
Ω^-conn m (S n) X pX =
  path-conn $ Ω^-conn (S m) n X $
    transport (λ k → is-connected k (fst X)) (! (+2+-βr ⟨ n ⟩₋₂ m)) pX

{- Eckmann-Hilton argument -}
module _ {i} {X : Ptd i} where

  Ω-fmap2-∙ : (α β : Ω^ 2 X) → ap2 _∙_ α β == Ω^S-∙ 1 α β
  Ω-fmap2-∙ α β = ap2-out _∙_ α β ∙ ap2 _∙_ (lemma α) (ap-idf β)
    where
    lemma : ∀ {i} {A : Type i} {x y : A} {p q : x == y} (α : p == q)
      → ap (λ r → r ∙ idp) α == ∙-unit-r p ∙ α ∙' ! (∙-unit-r q)
    lemma {p = idp} idp = idp

  ⊙Ω-fmap2-∙ : ⊙Ω-fmap2 (⊙Ω-∙ {X = X}) == ⊙Ω-∙
  ⊙Ω-fmap2-∙ = ⊙λ= (uncurry Ω-fmap2-∙) idp

  Ω^2-∙-comm : (α β : Ω^ 2 X) → Ω^S-∙ 1 α β == Ω^S-∙ 1 β α
  Ω^2-∙-comm α β = ! (⋆2=Ω^S-∙ α β) ∙ ⋆2=⋆'2 α β ∙ ⋆'2=Ω^S-∙ α β
    where
      ⋆2=Ω^S-∙ : (α β : Ω^ 2 X) → α ⋆2 β == Ω^S-∙ 1 α β
      ⋆2=Ω^S-∙ α β = ap (λ π → π ∙ β) (∙-unit-r α)

      ⋆'2=Ω^S-∙ : (α β : Ω^ 2  X) → α ⋆'2 β == Ω^S-∙ 1 β α
      ⋆'2=Ω^S-∙ α β = ap (λ π → β ∙ π) (∙-unit-r α)

{- Pushing truncation through loop space -}
module _ {i} where

  Trunc-Ω^-conv : (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
    → ⊙Trunc m (⊙Ω^ n X) == ⊙Ω^ n (⊙Trunc (⟨ n ⟩₋₂ +2+ m) X)
  Trunc-Ω^-conv m O X = idp
  Trunc-Ω^-conv m (S n) X =
    ⊙Trunc m (⊙Ω^ (S n) X)
      =⟨ ! (pair= (Trunc=-path [ _ ] [ _ ]) (↓-idf-ua-in _ idp)) ⟩
    ⊙Ω (⊙Trunc (S m) (⊙Ω^ n X))
      =⟨ ap ⊙Ω (Trunc-Ω^-conv (S m) n X) ⟩
    ⊙Ω^ (S n) (⊙Trunc (⟨ n ⟩₋₂ +2+ S m) X)
      =⟨ +2+-βr ⟨ n ⟩₋₂ m |in-ctx (λ k → ⊙Ω^ (S n) (⊙Trunc k X)) ⟩
    ⊙Ω^ (S n) (⊙Trunc (S ⟨ n ⟩₋₂ +2+ m) X) =∎

  Ω-Trunc-econv : (m : ℕ₋₂) (X : Ptd i)
    → Ω (⊙Trunc (S m) X) ≃ Trunc m (Ω X)
  Ω-Trunc-econv m X = Trunc=-equiv [ snd X ] [ snd X ]

{- Our definition of Ω^ builds up loops on the outside,
 - but this is equivalent to building up on the inside -}
module _ {i} where
  ⊙Ω^-Ω-split : (n : ℕ) (X : Ptd i)
    → (⊙Ω^ (S n) X ⊙→ ⊙Ω^ n (⊙Ω X))
  ⊙Ω^-Ω-split O _ = (idf _ , idp)
  ⊙Ω^-Ω-split (S n) X = ⊙Ω-fmap (⊙Ω^-Ω-split n X)

  Ω^-Ω-split : (n : ℕ) (X : Ptd i)
    → (Ω^ (S n) X → Ω^ n (⊙Ω X))
  Ω^-Ω-split n X = fst (⊙Ω^-Ω-split n X)

  Ω^S-Ω-split-∙ : (n : ℕ)
    (X : Ptd i) (p q : Ω^ (S (S n)) X)
    → Ω^-Ω-split (S n) X (Ω^S-∙ (S n) p q)
      == Ω^S-∙ n (Ω^-Ω-split (S n) X p) (Ω^-Ω-split (S n) X q)
  Ω^S-Ω-split-∙ n X p q =
    Ω^S-fmap-∙ 0 (⊙Ω^-Ω-split n X) p q

  Ω^-Ω-split-is-equiv : (n : ℕ) (X : Ptd i)
    → is-equiv (Ω^-Ω-split n X)
  Ω^-Ω-split-is-equiv O X = is-eq (idf _) (idf _) (λ _ → idp) (λ _ → idp)
  Ω^-Ω-split-is-equiv (S n) X =
    ⊙Ω^-isemap 1 (⊙Ω^-Ω-split n X) (Ω^-Ω-split-is-equiv n X)

  Ω^-Ω-split-equiv : (n : ℕ) (X : Ptd i) → Ω^ (S n) X ≃ Ω^ n (⊙Ω X)
  Ω^-Ω-split-equiv n X = _ , Ω^-Ω-split-is-equiv n X
