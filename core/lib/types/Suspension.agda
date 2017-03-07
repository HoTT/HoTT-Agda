{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlip
open import lib.types.PushoutFmap
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Paths
open import lib.types.Truncation
open import lib.types.Lift
open import lib.cubical.Square

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  susp-span : Span
  susp-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Susp : Type i
  Susp = Pushout susp-span

  -- [north'] and [south'] explictly ask for [A]

  north' : Susp
  north' = left tt

  south' : Susp
  south' = right tt

module _ {i} {A : Type i} where

  north : Susp A
  north = north' A

  south : Susp A
  south = south' A

  merid : A → north == south
  merid x = glue x

  module SuspElim {j} {P : Susp A → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ]) where
    open module P = PushoutElim (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspElim public using () renaming (f to Susp-elim)

  module SuspRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    open module P = PushoutRec {d = susp-span A} (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspRec public using () renaming (f to Susp-rec)

  module SuspRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = susp-span A} (λ _ → n) (λ _ → s) p

susp-⊙span : ∀ {i} → Ptd i → ⊙Span
susp-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp ⊙[ A , _ ] = ⊙[ Susp A , north ]


σloop : ∀ {i} (X : Ptd i) → de⊙ X → north' (de⊙ X) == north' (de⊙ X)
σloop ⊙[ _ , x₀ ] x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (pt X) == idp
σloop-pt {X = ⊙[ _ , x₀ ]} = !-inv-r (merid x₀)


module SuspFlip {i} {A : Type i} = SuspRec
  (south' A) north (! ∘ merid)

Susp-flip : ∀ {i} {A : Type i} → Susp A → Susp A
Susp-flip = SuspFlip.f

⊙Susp-flip : ∀ {i} (X : Ptd i) → ⊙Susp X ⊙→ ⊙Susp X
⊙Susp-flip X = (Susp-flip , ! (merid (pt X)))

Susp-flip-equiv : ∀ {i} {A : Type i} → Susp A ≃ Susp A
Susp-flip-equiv {A = A} = Pushout-flip-equiv (susp-span A)

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspRec north south (merid ∘ f)

  Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Susp A → Susp B)
  Susp-fmap = SuspFmap.f

  ⊙Susp-fmap : {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙Susp X ⊙→ ⊙Susp Y
  ⊙Susp-fmap (f , fpt) = (Susp-fmap f , idp)

module _ {i} where

  Susp-fmap-idf : (A : Type i) → ∀ a → Susp-fmap (idf A) a == a
  Susp-fmap-idf A = Susp-elim idp idp $ λ a →
    ↓-='-in' (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙Susp-fmap-idf : (X : Ptd i)
    → ⊙Susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙Susp-fmap-idf X = ⊙λ= (Susp-fmap-idf (de⊙ X)) idp

module _ {i j} where

  Susp-fmap-cst : {A : Type i} {B : Type j} (b : B)
    (a : Susp A) → Susp-fmap (cst b) a == north
  Susp-fmap-cst b = Susp-elim idp (! (merid b)) $ (λ a →
    ↓-app=cst-from-square $ SuspFmap.merid-β (cst b) a ∙v⊡ tr-square _)

  ⊙Susp-fmap-cst : {X : Ptd i} {Y : Ptd j}
    → ⊙Susp-fmap (⊙cst {X = X} {Y = Y}) == ⊙cst
  ⊙Susp-fmap-cst = ⊙λ= (Susp-fmap-cst _) idp

  Susp-flip-fmap : {A : Type i} {B : Type j} (f : A → B)
    → ∀ σ → Susp-flip (Susp-fmap f σ) == Susp-fmap f (Susp-flip σ)
  Susp-flip-fmap f = Susp-elim idp idp $ λ y → ↓-='-in' $
    ap-∘ (Susp-fmap f) Susp-flip (merid y)
    ∙ ap (ap (Susp-fmap f)) (SuspFlip.merid-β y)
    ∙ ap-! (Susp-fmap f) (merid y)
    ∙ ap ! (SuspFmap.merid-β f y)
    ∙ ! (SuspFlip.merid-β (f y))
    ∙ ! (ap (ap Susp-flip) (SuspFmap.merid-β f y))
    ∙ ∘-ap Susp-flip (Susp-fmap f) (merid y)

module _ {i j k} where

  Susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
    (σ : Susp A) → Susp-fmap (g ∘ f) σ == Susp-fmap g (Susp-fmap f σ)
  Susp-fmap-∘ g f = Susp-elim
    idp
    idp
    (λ a → ↓-='-in' $
      ap-∘ (Susp-fmap g) (Susp-fmap f) (merid a)
      ∙ ap (ap (Susp-fmap g)) (SuspFmap.merid-β f a)
      ∙ SuspFmap.merid-β g (f a)
      ∙ ! (SuspFmap.merid-β (g ∘ f) a))

  ⊙Susp-fmap-∘ : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
    (g : Y ⊙→ Z) (f : X ⊙→ Y)
    → ⊙Susp-fmap (g ⊙∘ f) == ⊙Susp-fmap g ⊙∘ ⊙Susp-fmap f
  ⊙Susp-fmap-∘ g f = ⊙λ= (Susp-fmap-∘ (fst g) (fst f)) idp


{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtractGlue = PushoutRec {d = s} {D = Susp (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  extract-glue = ExtractGlue.f

  module _ {x₀ : Span.A s} where

    ⊙extract-glue : ⊙[ Pushout s , left x₀ ] ⊙→ ⊙[ Susp (Span.C s) , north ]
    ⊙extract-glue = extract-glue , idp

module _ {i j} {A : Type i} {B : Type j} (eq : A ≃ B) where

  susp-span-emap : SpanEquiv (susp-span A) (susp-span B)
  susp-span-emap = ( span-map (idf _) (idf _) (fst eq) (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
                  , idf-is-equiv _ , idf-is-equiv _ , snd eq)

  Susp-emap : Susp A ≃ Susp B
  Susp-emap = Pushout-emap susp-span-emap

  private
    -- This is to make sure that we did not screw up [Susp-emap].
    test₀ : fst Susp-emap == Susp-fmap (fst eq)
    test₀ = idp

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙Susp-emap : X ⊙≃ Y → ⊙Susp X ⊙≃ ⊙Susp Y
  ⊙Susp-emap ⊙eq = ≃-to-⊙≃ (Susp-emap (⊙≃-to-≃ ⊙eq)) idp

{- Interaction with [Lift] -}
module _ {i j} (X : Type i) where

  Susp-Lift-econv : Susp (Lift {j = j} X) ≃ Lift {j = j} (Susp X)
  Susp-Lift-econv = lift-equiv ∘e Susp-emap lower-equiv

  Susp-Lift-conv : Susp (Lift {j = j} X) == Lift {j = j} (Susp X)
  Susp-Lift-conv = ua Susp-Lift-econv

module _ {i j} (X : Ptd i) where

  ⊙Susp-Lift-econv : ⊙Susp (⊙Lift {j = j} X) ⊙≃ ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-Lift-econv = ⊙lift-equiv {j = j} ⊙∘e ⊙Susp-emap {X = ⊙Lift {j = j} X} {Y = X} ⊙lower-equiv

  ⊙Susp-Lift-conv : ⊙Susp (⊙Lift {j = j} X) == ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-Lift-conv = ⊙ua ⊙Susp-Lift-econv

{- Suspension of an n-connected space is n+1-connected -}
abstract
  Susp-conn : ∀ {i} {A : Type i} {n : ℕ₋₂}
    → is-connected n A → is-connected (S n) (Susp A)
  Susp-conn {A = A} {n = n} cA =
    ([ north ] ,
     Trunc-elim (λ _ → =-preserves-level Trunc-level)
       (Susp-elim
         idp
         (Trunc-rec (Trunc-level {n = S n} _ _)
                    (λ a → ap [_] (merid a))
                    (fst cA))
         (λ x → Trunc-elim
            {P = λ y → idp ==
              Trunc-rec (Trunc-level {n = S n} _ _) (λ a → ap [_] (merid a)) y
              [ (λ z → [ north ] == [ z ]) ↓ (merid x) ]}
            (λ _ → ↓-preserves-level (Trunc-level {n = S n} _ _))
            (λ x' → ↓-cst=app-in (∙'-unit-l _ ∙ mers-eq n cA x x'))
            (fst cA))))
    where
    mers-eq : ∀ {i} {A : Type i} (n : ℕ₋₂)
      → is-connected n A → (x x' : A)
      → ap ([_] {n = S n}) (merid x)
        == Trunc-rec (Trunc-level {n = S n} _ _)
                     (λ a → ap [_] (merid a)) [ x' ]
    mers-eq ⟨-2⟩ cA x x' = contr-has-all-paths (Trunc-level {n = -1} _ _) _ _
    mers-eq {A = A} (S n) cA x x' =
      conn-elim (pointed-conn-out A x cA)
        (λ y → ((ap [_] (merid x) == ap [_] (merid y)) ,
                Trunc-level {n = S (S n)} _ _ _ _))
        (λ _ → idp) x'
