{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Paths
open import lib.cubical.Square

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  suspension-span : Span
  suspension-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Suspension : Type i
  Suspension = Pushout suspension-span

  north : Suspension
  north = left tt

  south : Suspension
  south = right tt

  merid : A → north == south
  merid x = glue x

  module SuspensionElim {j} {P : Suspension → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ])
    = PushoutElim (λ _ → n) (λ _ → s) p

  open SuspensionElim public using () renaming (f to Suspension-elim)

  module SuspensionRec {j} {C : Type j} (n s : C) (p : A → n == s)
    = PushoutRec {d = suspension-span} (λ _ → n) (λ _ → s) p

  module SuspensionRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = suspension-span} (λ _ → n) (λ _ → s) p

suspension-⊙span : ∀ {i} → Ptd i → ⊙Span
suspension-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp (A , _) = ⊙[ Suspension A , north A ]


σloop : ∀ {i} (X : Ptd i) → fst X → north (fst X) == north (fst X)
σloop (_ , x₀) x = merid _ x ∙ ! (merid _ x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (snd X) == idp
σloop-pt {X = (_ , x₀)} = !-inv-r (merid _ x₀)


module FlipSusp {i} {A : Type i} = SuspensionRec A
  (south A) (north A) (! ∘ merid A)

flip-susp : ∀ {i} {A : Type i} → Suspension A → Suspension A
flip-susp = FlipSusp.f

⊙flip-susp : ∀ {i} (X : Ptd i) → fst (⊙Susp X ⊙→ ⊙Susp X)
⊙flip-susp X = (flip-susp , ! (merid _ (snd X)))

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspensionRec A (north B) (south B) (merid B ∘ f)

  susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Suspension A → Suspension B)
  susp-fmap = SuspFmap.f

  ⊙susp-fmap : {X : Ptd i} {Y : Ptd j} (f : fst (X ⊙→ Y))
    → fst (⊙Susp X ⊙→ ⊙Susp Y)
  ⊙susp-fmap (f , fpt) = (susp-fmap f , idp)

module _ {i} where

  susp-fmap-idf : (A : Type i) → ∀ a → susp-fmap (idf A) a == a
  susp-fmap-idf A = Suspension-elim _ idp idp $ λ a →
    ↓-='-in (ap-idf (merid _ a) ∙ ! (SuspFmap.glue-β (idf A) a))

  ⊙susp-fmap-idf : (X : Ptd i)
    → ⊙susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙susp-fmap-idf X = ⊙λ= (susp-fmap-idf (fst X)) idp

module _ {i j} where

  susp-fmap-cst : {A : Type i} {B : Type j} (b : B)
    (a : Suspension A) → susp-fmap (cst b) a == north _
  susp-fmap-cst b = Suspension-elim _ idp (! (merid _ b)) $ (λ a →
    ↓-app=cst-from-square $ SuspFmap.glue-β (cst b) a ∙v⊡ tr-square _)

  ⊙susp-fmap-cst : {X : Ptd i} {Y : Ptd j}
    → ⊙susp-fmap (⊙cst {X = X} {Y = Y}) == ⊙cst
  ⊙susp-fmap-cst = ⊙λ= (susp-fmap-cst _) idp

module _ {i j k} where

  susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
    (σ : Suspension A) → susp-fmap (g ∘ f) σ == susp-fmap g (susp-fmap f σ)
  susp-fmap-∘ g f = Suspension-elim _
    idp
    idp
    (λ a → ↓-='-in $
      ap-∘ (susp-fmap g) (susp-fmap f) (merid _ a)
      ∙ ap (ap (susp-fmap g)) (SuspFmap.glue-β f a)
      ∙ SuspFmap.glue-β g (f a)
      ∙ ! (SuspFmap.glue-β (g ∘ f) a))

  ⊙susp-fmap-∘ : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
    (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
    → ⊙susp-fmap (g ⊙∘ f) == ⊙susp-fmap g ⊙∘ ⊙susp-fmap f
  ⊙susp-fmap-∘ g f = ⊙λ= (susp-fmap-∘ (fst g) (fst f)) idp


{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtGlue = PushoutRec {d = s} {D = Suspension (Span.C s)}
    (λ _ → north _) (λ _ → south _) (merid _)

  ext-glue = ExtGlue.f

module _ {i j k} {s : Span {i} {j} {k}} {x₀ : Span.A s} where

  ⊙ext-glue :
    fst ((Pushout s , left x₀) ⊙→ (Suspension (Span.C s) , north _))
  ⊙ext-glue = (ext-glue , idp)
