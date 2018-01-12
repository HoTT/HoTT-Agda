{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.TLevel
open import lib.types.Pi
open import lib.types.Sigma
open import lib.NType2

module lib.types.Truncation where

module _ {i} where

  postulate  -- HIT
    Trunc : (n : ℕ₋₂) (A : Type i) → Type i
    [_] : {n : ℕ₋₂} {A : Type i} → A → Trunc n A
    instance Trunc-level : {n : ℕ₋₂} {A : Type i} → has-level n (Trunc n A)

  module TruncElim {n : ℕ₋₂} {A : Type i} {j} {P : Trunc n A → Type j}
    {{p : (x : Trunc n A) → has-level n (P x)}} (d : (a : A) → P [ a ]) where

    postulate  -- HIT
      f : Π (Trunc n A) P
      [_]-β : ∀ a → f [ a ] ↦ d a
    {-# REWRITE [_]-β #-}

open TruncElim public renaming (f to Trunc-elim)

module TruncRec {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {{p : has-level n B}}
  (d : A → B) where

  private
    module M = TruncElim {{λ x → p}} d

  f : Trunc n A → B
  f = M.f

open TruncRec public renaming (f to Trunc-rec)

module TruncRecType {i j} {n : ℕ₋₂} {A : Type i} (d : A → n -Type j) where

  open TruncRec {{n -Type-level j}} d public

  flattening-Trunc : Σ (Trunc (S n) A) (fst ∘ f) ≃ Trunc (S n) (Σ A (fst ∘ d))
  flattening-Trunc = equiv to from to-from from-to where

    to-aux : (x : Trunc (S n) A) → (fst (f x) → Trunc (S n) (Σ A (fst ∘ d)))
    to-aux = Trunc-elim (λ a b → [ (a , b) ])

    to : Σ (Trunc (S n) A) (fst ∘ f) → Trunc (S n) (Σ A (fst ∘ d))
    to (x , y) = to-aux x y

    from-aux : Σ A (fst ∘ d) → Σ (Trunc (S n) A) (fst ∘ f)
    from-aux (a , b) = ([ a ] , b)

    from : Trunc (S n) (Σ A (fst ∘ d)) → Σ (Trunc (S n) A) (fst ∘ f)
    from = Trunc-rec {{Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))}}
                     from-aux  where

    to-from : (x : Trunc (S n) (Σ A (fst ∘ d))) → to (from x) == x
    to-from = Trunc-elim (λ _ → idp)

    from-to-aux : (a : Trunc (S n) A) (b : fst (f a)) → from (to-aux a b) == (a , b)
    from-to-aux = Trunc-elim {{λ _ → Π-level (λ _ → =-preserves-level (Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))))}}
                             (λ a b → idp)

    from-to : (x : Σ (Trunc (S n) A) (fst ∘ f)) → from (to x) == x
    from-to (a , b) = from-to-aux a b


⊙Trunc : ∀ {i} → ℕ₋₂ → Ptd i → Ptd i
⊙Trunc n ⊙[ A , a ] = ⊙[ Trunc n A , [ a ] ]


module _ {i} {n : ℕ₋₂} {A : Type i} where

  Trunc= : (a b : Trunc (S n) A) → n -Type i
  Trunc= = Trunc-elim (λ a → Trunc-elim ((λ b → (Trunc n (a == b) , Trunc-level))))

  Trunc=-equiv : (a b : Trunc (S n) A) → (a == b) ≃ fst (Trunc= a b)
  Trunc=-equiv a b = equiv (to a b) (from a b) (to-from a b) (from-to a b) where

    to-aux : (a : Trunc (S n) A) → fst (Trunc= a a)
    to-aux = Trunc-elim {{λ x → raise-level _ (snd (Trunc= x x))}}
                        (λ a → [ idp ])

    to : (a b : Trunc (S n) A) → (a == b → fst (Trunc= a b))
    to a .a idp = to-aux a

    from-aux : (a b : A) → a == b → [ a ] == [ b ] :> Trunc (S n) A
    from-aux a .a idp = idp

    from : (a b : Trunc (S n) A) → (fst (Trunc= a b) → a == b)
    from = Trunc-elim (λ a → Trunc-elim (λ b → Trunc-rec (from-aux a b)))

    to-from-aux : (a b : A) → (p : a == b) → to _ _ (from-aux a b p) == [ p ]
    to-from-aux a .a idp = idp

    to-from : (a b : Trunc (S n) A) (x : fst (Trunc= a b)) → to a b (from a b x) == x
    to-from = Trunc-elim {{λ x → Π-level (λ y → Π-level (λ _ → =-preserves-level (raise-level _ (snd (Trunc= x y)))))}}
              (λ a → Trunc-elim {{λ x → Π-level (λ _ → =-preserves-level (raise-level _ (snd (Trunc= [ a ] x))))}}
              (λ b → Trunc-elim
              (to-from-aux a b)))

    from-to-aux : (a : Trunc (S n) A) → from a a (to-aux a) == idp
    from-to-aux = Trunc-elim (λ _ → idp)

    from-to : (a b : Trunc (S n) A) (p : a == b) → from a b (to a b p) == p
    from-to a .a idp = from-to-aux a
  Trunc=-path : (a b : Trunc (S n) A) → (a == b) == fst (Trunc= a b)
  Trunc=-path a b = ua (Trunc=-equiv a b)

{- Universal property -}

abstract
  Trunc-rec-is-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
    {{p : has-level n B}} → is-equiv (Trunc-rec {{p}} :> ((A → B) → (Trunc n A → B)))
  Trunc-rec-is-equiv n A B {{p}} = is-eq _ (λ f → f ∘ [_])
    (λ f → λ= (Trunc-elim (λ a → idp))) (λ f → idp)


Trunc-preserves-level : ∀ {i} {A : Type i} {n : ℕ₋₂} (m : ℕ₋₂)
 → has-level n A → has-level n (Trunc m A)
Trunc-preserves-level {n = ⟨-2⟩} _ p = has-level-in
  ([ contr-center p ] , Trunc-elim (λ a → ap [_] (contr-path p a)))
Trunc-preserves-level ⟨-2⟩ _ = contr-has-level Trunc-level
Trunc-preserves-level {n = (S n)} (S m) c = has-level-in (λ t₁ t₂ →
  Trunc-elim
    {{λ s₁ → prop-has-level-S {A = has-level n (s₁ == t₂)} has-level-is-prop}}
    (λ a₁ → Trunc-elim
      {{λ s₂ → prop-has-level-S {A = has-level n ([ a₁ ] == s₂)} has-level-is-prop}}
      (λ a₂ → equiv-preserves-level
      ((Trunc=-equiv [ a₁ ] [ a₂ ])⁻¹)
               {{Trunc-preserves-level {n = n} m (has-level-apply c a₁ a₂)}})
              t₂)
    t₁)

{- an n-type is equivalent to its n-truncation -}
unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (A : Type i)
  {{_ : has-level n A}} → Trunc n A ≃ A
unTrunc-equiv A = equiv f [_] (λ _ → idp) g-f where
  f = Trunc-rec (idf _)
  g-f = Trunc-elim (λ _ → idp)

⊙unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (X : Ptd i)
  {{_ : has-level n (de⊙ X)}} → ⊙Trunc n X ⊙≃ X
⊙unTrunc-equiv {n = n} X = ≃-to-⊙≃ (unTrunc-equiv (de⊙ X)) idp

-- Equivalence associated to the universal property
Trunc-extend-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
  {{p : has-level n B}} → (A → B) ≃ (Trunc n A → B)
Trunc-extend-equiv n A B = (Trunc-rec , Trunc-rec-is-equiv n A B)

Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} → ((A → B) → (Trunc n A → Trunc n B))
Trunc-fmap f = Trunc-rec ([_] ∘ f)

⊙Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} → ((X ⊙→ Y) → (⊙Trunc n X ⊙→ ⊙Trunc n Y))
⊙Trunc-fmap F = Trunc-fmap (fst F) , ap [_] (snd F)

Trunc-fmap2 : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → ((A → B → C) → (Trunc n A → Trunc n B → Trunc n C))
Trunc-fmap2 f = Trunc-rec (λ a → Trunc-fmap (f a))

-- XXX What is the naming convention?
Trunc-fpmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {f g : A → B} (h : (a : A) → f a == g a)
  → ((a : Trunc n A) → Trunc-fmap f a == Trunc-fmap g a)
Trunc-fpmap h = Trunc-elim (ap [_] ∘ h)

Trunc-fmap-idf : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → ∀ x → Trunc-fmap {n = n} (idf A) x == x
Trunc-fmap-idf =
  Trunc-elim (λ _ → idp)

Trunc-fmap-∘ : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → (g : B → C) → (f : A → B)
  → ∀ x → Trunc-fmap {n = n} g (Trunc-fmap f x) == Trunc-fmap (g ∘ f) x
Trunc-fmap-∘ g f =
  Trunc-elim (λ _ → idp)

{- Pushing concatentation through Trunc= -}
module _ {i} {n : ℕ₋₂} {A : Type i} where

  {- concatenation in Trunc= -}
  Trunc=-∙ : {ta tb tc : Trunc (S n) A}
    → fst (Trunc= ta tb) → fst (Trunc= tb tc) → fst (Trunc= ta tc)
  Trunc=-∙ {ta = ta} {tb = tb} {tc = tc} =
    Trunc-elim {P = λ ta → C ta tb tc}
      {{λ ta → level ta tb tc}}
      (λ a → Trunc-elim {P = λ tb → C [ a ] tb tc}
         {{λ tb → level [ a ] tb tc}}
         (λ b → Trunc-elim {P = λ tc → C [ a ] [ b ] tc}
                  {{λ tc → level [ a ] [ b ] tc}}
                  (λ c → Trunc-fmap2 _∙_)
                  tc)
         tb)
      ta
    where
    C : (ta tb tc : Trunc (S n) A) → Type i
    C ta tb tc = fst (Trunc= ta tb) → fst (Trunc= tb tc) → fst (Trunc= ta tc)

    level : (ta tb tc : Trunc (S n) A) → has-level (S n) (C ta tb tc)
    level ta tb tc = raise-level _ $
              Π-level (λ _ → Π-level (λ _ → snd (Trunc= ta tc)))

  Trunc=-∙-comm : {x y z : Trunc (S n) A }
    (p : x == y) (q : y == z)
    →  –> (Trunc=-equiv x z) (p ∙ q)
    == Trunc=-∙ {ta = x} (–> (Trunc=-equiv x y) p) (–> (Trunc=-equiv y z) q)
  Trunc=-∙-comm {x = x} idp idp =
    Trunc-elim
       {P = λ x → –> (Trunc=-equiv x x) idp
               == Trunc=-∙ {ta = x} (–> (Trunc=-equiv x x) idp)
                                    (–> (Trunc=-equiv x x) idp)}
       {{λ x → raise-level _ $ =-preserves-level (snd (Trunc= x x))}}
       (λ a → idp)
       x

{- naturality of Trunc=-equiv -}

module _ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} (f : A → B) where
  Trunc=-fmap : ∀ (a₀ a₁ : Trunc (S n) A)
    → (fst (Trunc= {n = n} a₀ a₁) → fst (Trunc= {n = n} (Trunc-fmap f a₀) (Trunc-fmap f a₁)))
  Trunc=-fmap = Trunc-elim
    {P = λ a₀ → ∀ a₁ → (fst (Trunc= a₀ a₁) → fst (Trunc= (Trunc-fmap f a₀) (Trunc-fmap f a₁)))}
    {{λ a₀ → Π-level λ a₁ → Π-level λ _ → raise-level _ $ snd (Trunc= (Trunc-fmap f a₀) (Trunc-fmap f a₁))}}
    (λ a₀ → Trunc-elim
      {P = λ a₁ → (fst (Trunc= [ a₀ ] a₁) → fst (Trunc= [ f a₀ ] (Trunc-fmap f a₁)))}
      {{λ a₁ → Π-level λ _ → raise-level _ $ snd (Trunc= [ f a₀ ] (Trunc-fmap f a₁))}}
      (λ a₁ → Trunc-fmap (ap f)))

module _ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} (f : A → B) where
  Trunc=-equiv-nat : ∀ (a₀ a₁ : Trunc (S n) A) (p : a₀ == a₁)
     →  –> (Trunc=-equiv (Trunc-fmap f a₀) (Trunc-fmap f a₁)) (ap (Trunc-fmap f) p)
     == Trunc=-fmap f a₀ a₁ (–> (Trunc=-equiv a₀ a₁) p)
  Trunc=-equiv-nat a₀ .a₀ idp =
    Trunc-elim
      {P = λ a
        →  –> (Trunc=-equiv (Trunc-fmap f a) (Trunc-fmap f a)) idp
        == Trunc=-fmap f a a (–> (Trunc=-equiv a a) idp)}
      {{λ a → raise-level _ $ =-preserves-level $ snd ((Trunc= (Trunc-fmap f a) (Trunc-fmap f a)))}}
      (λ _ → idp)
      a₀

{- Truncation preserves equivalences - more convenient than univalence+ap
 - when we need to know the forward or backward function explicitly -}
module _ {i j} (n : ℕ₋₂) {A : Type i} {B : Type j} where

  Trunc-isemap : {f : A → B} → is-equiv f → is-equiv (Trunc-fmap {n = n} f)
  Trunc-isemap {f-orig} ie = is-eq f g f-g g-f where
    f = Trunc-fmap f-orig
    g = Trunc-fmap (is-equiv.g ie)

    f-g : ∀ tb → f (g tb) == tb
    f-g = Trunc-elim (ap [_] ∘ is-equiv.f-g ie)

    g-f : ∀ ta → g (f ta) == ta
    g-f = Trunc-elim (ap [_] ∘ is-equiv.g-f ie)

  Trunc-emap : A ≃ B → Trunc n A ≃ Trunc n B
  Trunc-emap (f , f-ie) = Trunc-fmap f , Trunc-isemap f-ie

transport-Trunc : ∀ {i j} {A : Type i} {n : ℕ₋₂} (P : A → Type j)
  {x y : A} (p : x == y) (b : P x)
  → transport (Trunc n ∘ P) p [ b ] == [ transport P p b ]
transport-Trunc _ idp _ = idp

Trunc-fuse : ∀ {i} (A : Type i) (m n : ℕ₋₂)
  → Trunc m (Trunc n A) ≃ Trunc (minT m n) A
Trunc-fuse A m n = equiv
  (Trunc-rec {{raise-level-≤T (minT≤l m n) Trunc-level}}
    (Trunc-rec {{raise-level-≤T (minT≤r m n) Trunc-level}}
      [_]))
  (Trunc-rec ([_] ∘ [_]))
  (Trunc-elim (λ _ → idp))
  (Trunc-elim (Trunc-elim
       {{λ _ → =-preserves-level (Trunc-preserves-level _ Trunc-level)}}
       (λ _ → idp)))
  where
      instance 
        l : has-level (minT m n) (Trunc m (Trunc n A))
        l with (minT-out m n)
        l | inl p = transport (λ k → has-level k (Trunc m (Trunc n A)))
                              (! p) Trunc-level
        l | inr q = Trunc-preserves-level _
                      (transport (λ k → has-level k (Trunc n A))
                                 (! q) Trunc-level)

Trunc-fuse-≤ : ∀ {i} (A : Type i) {m n : ℕ₋₂} (m≤n : m ≤T n)
  → Trunc m (Trunc n A) ≃ Trunc m A
Trunc-fuse-≤ A m≤n = equiv
  (Trunc-rec (Trunc-rec {{raise-level-≤T m≤n Trunc-level}}
      [_]))
  (Trunc-rec ([_] ∘ [_]))
  (Trunc-elim (λ _ → idp))
  (Trunc-elim (Trunc-elim
       {{λ _ → =-preserves-level (Trunc-preserves-level _ Trunc-level)}}
       (λ _ → idp)))

{- Truncating a binary product is equivalent to truncating its components -}
Trunc-×-econv : ∀ {i} {j} (n : ℕ₋₂) (A : Type i) (B : Type j)
  → Trunc n (A × B) ≃ Trunc n A × Trunc n B
Trunc-×-econv n A B = equiv f g f-g g-f
  where
  f : Trunc n (A × B) → Trunc n A × Trunc n B
  f = Trunc-rec (λ {(a , b) → [ a ] , [ b ]})

  g : Trunc n A × Trunc n B → Trunc n (A × B)
  g (ta , tb) = Trunc-rec (λ a → Trunc-rec (λ b → [ a , b ]) tb) ta

  f-g : ∀ p → f (g p) == p
  f-g (ta , tb) = Trunc-elim
    {P = λ ta → f (g (ta , tb)) == (ta , tb)}
    (λ a → Trunc-elim
      {P = λ tb → f (g ([ a ] , tb)) == ([ a ] , tb)}
      (λ b → idp)
      tb)
    ta

  g-f : ∀ tab → g (f tab) == tab
  g-f = Trunc-elim
    {P = λ tab → g (f tab) == tab}
    (λ ab → idp)

Trunc-×-conv : ∀ {i} {j} (n : ℕ₋₂) (A : Type i) (B : Type j)
  → Trunc n (A × B) == Trunc n A × Trunc n B
Trunc-×-conv n A B = ua (Trunc-×-econv n A B)
