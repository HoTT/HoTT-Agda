{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Empty
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.cubical.Square

module lib.types.LoopSpace where

module _ {i} where

  ⊙Ω : Ptd i → Ptd i
  ⊙Ω (A , a) = ⊙[ (a == a) , idp ]

  Ω : Ptd i → Type i
  Ω = fst ∘ ⊙Ω

  ⊙Ω^ : (n : ℕ) → Ptd i → Ptd i
  ⊙Ω^ O X = X
  ⊙Ω^ (S n) X = ⊙Ω (⊙Ω^ n X)

  Ω^ : (n : ℕ) → Ptd i → Type i
  Ω^ n X = fst (⊙Ω^ n X)

idp^ : ∀ {i} (n : ℕ) {X : Ptd i} → Ω^ n X
idp^ n {X} = snd (⊙Ω^ n X)

{- for n ≥ 1, we have a group structure on the loop space -}
module _ {i} where
  !^ : (n : ℕ) (t : n ≠ O) {X : Ptd i} → Ω^ n X → Ω^ n X
  !^ O t = ⊥-rec (t idp)
  !^ (S n) _ = !

  conc^ : (n : ℕ) (t : n ≠ O) {X : Ptd i} → Ω^ n X → Ω^ n X → Ω^ n X
  conc^ O t = ⊥-rec (t idp)
  conc^ (S n) _ = _∙_

{- pointed versions of functions on paths -}

private
  pt-lemma : ∀ {i} {A : Type i} {x y : A} (p : x == y)
    → ! p ∙ (idp ∙' p) == idp
  pt-lemma idp = idp

⊙conc : ∀ {i} {X : Ptd i} → fst (⊙Ω X ⊙× ⊙Ω X ⊙→ ⊙Ω X)
⊙conc = (uncurry _∙_ , idp)

⊙ap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → fst (X ⊙→ Y) → fst (⊙Ω X ⊙→ ⊙Ω Y)
⊙ap (f , fpt) = ((λ p → ! fpt ∙ ap f p ∙' fpt) , pt-lemma fpt)

⊙ap2 : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → fst (X ⊙× Y ⊙→ Z) → fst (⊙Ω X ⊙× ⊙Ω Y ⊙→ ⊙Ω Z)
⊙ap2 (f , fpt) = ((λ {(p , q) → ! fpt ∙ ap2 (curry f) p q ∙' fpt}) ,
                  pt-lemma fpt)

⊙ap-∘ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
  → ⊙ap (g ⊙∘ f) == ⊙ap g ⊙∘ ⊙ap f
⊙ap-∘ (g , idp) (f , idp) = ⊙λ= (λ p → ap-∘ g f p) idp

⊙ap-idf : ∀ {i} {X : Ptd i} → ⊙ap (⊙idf X) == ⊙idf _
⊙ap-idf = ⊙λ= ap-idf idp

⊙ap2-fst : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙ap2 {X = X} {Y = Y} ⊙fst == ⊙fst
⊙ap2-fst = ⊙λ= (uncurry ap2-fst) idp

⊙ap2-snd : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙ap2 {X = X} {Y = Y} ⊙snd == ⊙snd
⊙ap2-snd = ⊙λ= (uncurry ap2-snd) idp

⊙ap-ap2 : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : fst (Z ⊙→ W)) (F : fst (X ⊙× Y ⊙→ Z))
  → ⊙ap G ⊙∘ ⊙ap2 F == ⊙ap2 (G ⊙∘ F)
⊙ap-ap2 (g , idp) (f , idp) =
  ⊙λ= (uncurry (ap-ap2 g (curry f))) idp

⊙ap2-ap : ∀ {i j k l m}
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : fst ((U ⊙× V) ⊙→ Z)) (F₁ : fst (X ⊙→ U)) (F₂ : fst (Y ⊙→ V))
  → ⊙ap2 G ⊙∘ pair⊙→ (⊙ap F₁) (⊙ap F₂) == ⊙ap2 (G ⊙∘ pair⊙→ F₁ F₂)
⊙ap2-ap (g , idp) (f₁ , idp) (f₂ , idp) =
  ⊙λ= (λ {(p , q) → ap2-ap-l (curry g) f₁ p (ap f₂ q)
                  ∙ ap2-ap-r (λ x v → g (f₁ x , v)) f₂ p q})
      idp

⊙ap2-diag : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : fst (X ⊙× X ⊙→ Y))
  → ⊙ap2 F ⊙∘ ⊙diag == ⊙ap (F ⊙∘ ⊙diag)
⊙ap2-diag (f , idp) = ⊙λ= (ap2-diag (curry f)) idp

{- ap and ap2 for higher loop spaces -}

ap^ : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → fst (X ⊙→ Y) → fst (⊙Ω^ n X ⊙→ ⊙Ω^ n Y)
ap^ O F = F
ap^ (S n) F = ⊙ap (ap^ n F)

ap2^ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → fst ((X ⊙× Y) ⊙→ Z)
  → fst ((⊙Ω^ n X ⊙× ⊙Ω^ n Y) ⊙→ ⊙Ω^ n Z)
ap2^ O F = F
ap2^ (S n) F = ⊙ap2 (ap2^ n F)

ap^-idf : ∀ {i} (n : ℕ) {X : Ptd i} → ap^ n (⊙idf X) == ⊙idf _
ap^-idf O = idp
ap^-idf (S n) = ap ⊙ap (ap^-idf n) ∙ ⊙ap-idf

ap^-ap2^ : ∀ {i j k l} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : fst (Z ⊙→ W)) (F : fst ((X ⊙× Y) ⊙→ Z))
  → ap^ n G ⊙∘ ap2^ n F == ap2^ n (G ⊙∘ F)
ap^-ap2^ O G F = idp
ap^-ap2^ (S n) G F = ⊙ap-ap2 (ap^ n G) (ap2^ n F) ∙ ap ⊙ap2 (ap^-ap2^ n G F)

ap2^-fst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ap2^ n {X} {Y} ⊙fst == ⊙fst
ap2^-fst O = idp
ap2^-fst (S n) = ap ⊙ap2 (ap2^-fst n) ∙ ⊙ap2-fst

ap2^-snd : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ap2^ n {X} {Y} ⊙snd == ⊙snd
ap2^-snd O = idp
ap2^-snd (S n) = ap ⊙ap2 (ap2^-snd n) ∙ ⊙ap2-snd

ap2^-ap^ : ∀ {i j k l m} (n : ℕ)
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : fst ((U ⊙× V) ⊙→ Z)) (F₁ : fst (X ⊙→ U)) (F₂ : fst (Y ⊙→ V))
  → ap2^ n G ⊙∘ pair⊙→ (ap^ n F₁) (ap^ n F₂) == ap2^ n (G ⊙∘ pair⊙→ F₁ F₂)
ap2^-ap^ O G F₁ F₂ = idp
ap2^-ap^ (S n) G F₁ F₂ =
  ⊙ap2-ap (ap2^ n G) (ap^ n F₁) (ap^ n F₂) ∙ ap ⊙ap2 (ap2^-ap^ n G F₁ F₂)

ap2^-diag : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j} (F : fst (X ⊙× X ⊙→ Y))
  → ap2^ n F ⊙∘ ⊙diag == ap^ n (F ⊙∘ ⊙diag)
ap2^-diag O F = idp
ap2^-diag (S n) F = ⊙ap2-diag (ap2^ n F) ∙ ap ⊙ap (ap2^-diag n F)


module _ {i} {X : Ptd i} where

  {- Prove these as lemmas now
   - so we don't have to deal with the n = O case later -}

  conc^-unit-l : (n : ℕ) (t : n ≠ O) (q : Ω^ n X)
    → (conc^ n t (idp^ n) q) == q
  conc^-unit-l O t _ = ⊥-rec (t idp)
  conc^-unit-l (S n) _ _ = idp

  conc^-unit-r : (n : ℕ) (t : n ≠ O) (q : Ω^ n X)
    → (conc^ n t q (idp^ n)) == q
  conc^-unit-r O t = ⊥-rec (t idp)
  conc^-unit-r (S n) _ = ∙-unit-r

  conc^-assoc : (n : ℕ) (t : n ≠ O) (p q r : Ω^ n X)
    → conc^ n t (conc^ n t p q) r == conc^ n t p (conc^ n t q r)
  conc^-assoc O t = ⊥-rec (t idp)
  conc^-assoc (S n) _ = ∙-assoc

  !^-inv-l : (n : ℕ) (t : n ≠ O) (p : Ω^ n X)
    → conc^ n t (!^ n t p) p == idp^ n
  !^-inv-l O t = ⊥-rec (t idp)
  !^-inv-l (S n) _ = !-inv-l

  !^-inv-r : (n : ℕ) (t : n ≠ O) (p : Ω^ n X)
    → conc^ n t p (!^ n t p) == idp^ n
  !^-inv-r O t = ⊥-rec (t idp)
  !^-inv-r (S n) _ = !-inv-r

abstract
  ap^-conc^ : ∀ {i j} (n : ℕ) (t : n ≠ O)
    {X : Ptd i} {Y : Ptd j} (F : fst (X ⊙→ Y)) (p q : Ω^ n X)
    → fst (ap^ n F) (conc^ n t p q)
      == conc^ n t (fst (ap^ n F) p) (fst (ap^ n F) q)
  ap^-conc^ O t _ _ _ = ⊥-rec (t idp)
  ap^-conc^ (S n) _ {X = X} {Y = Y} F p q =
    ! gpt ∙ ap g (p ∙ q) ∙' gpt
      =⟨ ap-∙ g p q |in-ctx (λ w → ! gpt ∙ w ∙' gpt) ⟩
    ! gpt ∙ (ap g p ∙ ap g q) ∙' gpt
      =⟨ lemma (ap g p) (ap g q) gpt ⟩
    (! gpt ∙ ap g p ∙' gpt) ∙ (! gpt ∙ ap g q ∙' gpt) ∎
    where
    g : Ω^ n X → Ω^ n Y
    g = fst (ap^ n F)

    gpt : g (idp^ n) == idp^ n
    gpt = snd (ap^ n F)

    lemma : ∀ {i} {A : Type i} {x y : A}
      → (p q : x == x) (r : x == y)
      → ! r ∙ (p ∙ q) ∙' r == (! r ∙ p ∙' r) ∙ (! r ∙ q ∙' r)
    lemma p q idp = idp

{- ap^ preserves (pointed) equivalences -}
module _ {i j} {X : Ptd i} {Y : Ptd j} where

  is-equiv-ap^ : (n : ℕ) (F : fst (X ⊙→ Y)) (e : is-equiv (fst F))
    → is-equiv (fst (ap^ n F))
  is-equiv-ap^ O F e = e
  is-equiv-ap^ (S n) F e =
         pre∙-is-equiv (! (snd (ap^ n F)))
    ∘ise post∙'-is-equiv (snd (ap^ n F))
    ∘ise snd (equiv-ap (_ , is-equiv-ap^ n F e) _ _)

  equiv-ap^ : (n : ℕ) (F : fst (X ⊙→ Y)) (e : is-equiv (fst F))
    → Ω^ n X ≃ Ω^ n Y
  equiv-ap^ n F e = (fst (ap^ n F) , is-equiv-ap^ n F e)

Ω^-level-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (has-level (⟨ n ⟩₋₂ +2+ m) (fst X) → has-level m (Ω^ n X))
Ω^-level-in m O X pX = pX
Ω^-level-in m (S n) X pX =
  Ω^-level-in (S m) n X
    (transport (λ k → has-level k (fst X)) (! (+2+-βr ⟨ n ⟩₋₂ m)) pX)
    (idp^ n) (idp^ n)

Ω^-conn-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
  → (is-connected (⟨ n ⟩₋₂ +2+ m) (fst X)) → is-connected m (Ω^ n X)
Ω^-conn-in m O X pX = pX
Ω^-conn-in m (S n) X pX =
  path-conn $ Ω^-conn-in (S m) n X $
    transport (λ k → is-connected k (fst X)) (! (+2+-βr ⟨ n ⟩₋₂ m)) pX

{- Eckmann-Hilton argument -}
module _ {i} {X : Ptd i} where

  ap2-conc-is-conc : (α β : Ω^ 2 X) → ap2 _∙_ α β == conc^ 2 (ℕ-S≠O _) α β
  ap2-conc-is-conc α β = ap2-out _∙_ α β ∙ ap2 _∙_ (lemma α) (ap-idf β)
    where
    lemma : ∀ {i} {A : Type i} {x y : A} {p q : x == y} (α : p == q)
      → ap (λ r → r ∙ idp) α == ∙-unit-r p ∙ α ∙' ! (∙-unit-r q)
    lemma {p = idp} idp = idp

  ⊙ap2-conc-is-conc : ⊙ap2 (⊙conc {X = X}) == ⊙conc
  ⊙ap2-conc-is-conc = ⊙λ= (uncurry ap2-conc-is-conc) idp

  conc^2-comm : (α β : Ω^ 2 X) → conc^ 2 (ℕ-S≠O _) α β == conc^ 2 (ℕ-S≠O _) β α
  conc^2-comm α β = ! (⋆2=conc^ α β) ∙ ⋆2=⋆'2 α β ∙ ⋆'2=conc^ α β
    where
      ⋆2=conc^ : (α β : Ω^ 2 X) → α ⋆2 β == conc^ 2 (ℕ-S≠O _) α β
      ⋆2=conc^ α β = ap (λ π → π ∙ β) (∙-unit-r α)

      ⋆'2=conc^ : (α β : Ω^ 2  X) → α ⋆'2 β == conc^ 2 (ℕ-S≠O _) β α
      ⋆'2=conc^ α β = ap (λ π → β ∙ π) (∙-unit-r α)

{- Pushing truncation through loop space -}
module _ {i} where

  Trunc-Ω^ : (m : ℕ₋₂) (n : ℕ) (X : Ptd i)
    → ⊙Trunc m (⊙Ω^ n X) == ⊙Ω^ n (⊙Trunc (⟨ n ⟩₋₂ +2+ m) X)
  Trunc-Ω^ m O X = idp
  Trunc-Ω^ m (S n) X =
    ⊙Trunc m (⊙Ω^ (S n) X)
      =⟨ ! (pair= (Trunc=-path [ _ ] [ _ ]) (↓-idf-ua-in _ idp)) ⟩
    ⊙Ω (⊙Trunc (S m) (⊙Ω^ n X))
      =⟨ ap ⊙Ω (Trunc-Ω^ (S m) n X) ⟩
    ⊙Ω^ (S n) (⊙Trunc (⟨ n ⟩₋₂ +2+ S m) X)
      =⟨ +2+-βr ⟨ n ⟩₋₂ m |in-ctx (λ k → ⊙Ω^ (S n) (⊙Trunc k X)) ⟩
    ⊙Ω^ (S n) (⊙Trunc (S ⟨ n ⟩₋₂ +2+ m) X) ∎

  Ω-Trunc-equiv : (m : ℕ₋₂) (X : Ptd i)
    → Ω (⊙Trunc (S m) X) ≃ Trunc m (Ω X)
  Ω-Trunc-equiv m X = Trunc=-equiv [ snd X ] [ snd X ]

{- A loop space is a pregroup, and a group if it has the right level -}
module _ {i} (n : ℕ) (t : n ≠ O) (X : Ptd i) where

  Ω^-group-structure : GroupStructure (Ω^ n X)
  Ω^-group-structure = record {
    ident = idp^ n;
    inv = !^ n t;
    comp = conc^ n t;
    unitl = conc^-unit-l n t;
    unitr = conc^-unit-r n t;
    assoc = conc^-assoc n t;
    invr = !^-inv-r n t;
    invl = !^-inv-l n t
    }

  Ω^-Group : has-level ⟨ n ⟩ (fst X) → Group i
  Ω^-Group pX = group
    (Ω^ n X)
    (Ω^-level-in 0 n X $
       transport (λ t → has-level t (fst X)) (+2+-comm 0 ⟨ n ⟩₋₂) pX)
    Ω^-group-structure

{- Our definition of Ω^ builds up loops on the outside,
 - but this is equivalent to building up on the inside -}
module _ {i} where
  ⊙Ω^-inner-path : (n : ℕ) (X : Ptd i)
    → ⊙Ω^ (S n) X == ⊙Ω^ n (⊙Ω X)
  ⊙Ω^-inner-path O X = idp
  ⊙Ω^-inner-path (S n) X = ap ⊙Ω (⊙Ω^-inner-path n X)

  ⊙Ω^-inner-out : (n : ℕ) (X : Ptd i)
    → fst (⊙Ω^ (S n) X ⊙→ ⊙Ω^ n (⊙Ω X))
  ⊙Ω^-inner-out O _ = (idf _ , idp)
  ⊙Ω^-inner-out (S n) X = ap^ 1 (⊙Ω^-inner-out n X)

  Ω^-inner-out : (n : ℕ) (X : Ptd i)
    → (Ω^ (S n) X → Ω^ n (⊙Ω X))
  Ω^-inner-out n X = fst (⊙Ω^-inner-out n X)

  Ω^-inner-out-conc^ : (n : ℕ) (t : n ≠ O)
    (X : Ptd i) (p q : Ω^ (S n) X)
    → Ω^-inner-out n X (conc^ (S n) (ℕ-S≠O _) p q)
      == conc^ n t (Ω^-inner-out n X p) (Ω^-inner-out n X q)
  Ω^-inner-out-conc^ O t X _ _ = ⊥-rec (t idp)
  Ω^-inner-out-conc^ (S n) t X p q =
    ap^-conc^ 1 (ℕ-S≠O _) (⊙Ω^-inner-out n X) p q

  Ω^-inner-is-equiv : (n : ℕ) (X : Ptd i)
    → is-equiv (fst (⊙Ω^-inner-out n X))
  Ω^-inner-is-equiv O X = is-eq (idf _) (idf _) (λ _ → idp) (λ _ → idp)
  Ω^-inner-is-equiv (S n) X =
    is-equiv-ap^ 1 (⊙Ω^-inner-out n X) (Ω^-inner-is-equiv n X)

  Ω^-inner-equiv : (n : ℕ) (X : Ptd i) → Ω^ (S n) X ≃ Ω^ n (⊙Ω X)
  Ω^-inner-equiv n X = _ , Ω^-inner-is-equiv n X
