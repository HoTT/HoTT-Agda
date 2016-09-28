{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.Unit
open import lib.types.Paths
open import lib.types.Lift
open import lib.cubical.Square

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  suspension-span : Span
  suspension-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Suspension : Type i
  Suspension = Pushout suspension-span

  Susp = Suspension

  -- [north'] and [south'] explictly ask for [A]

  north' : Suspension
  north' = left tt

  south' : Suspension
  south' = right tt

module _ {i} {A : Type i} where

  north : Suspension A
  north = north' A

  south : Suspension A
  south = south' A

  merid : A → north == south
  merid x = glue x

  module SuspensionElim {j} {P : Suspension A → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ]) where
    open module P = PushoutElim (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)
  module SuspElim = SuspensionElim

  open SuspensionElim public using () renaming (f to Suspension-elim)
  Susp-elim = Suspension-elim

  module SuspensionRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    open module P = PushoutRec {d = suspension-span A} (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)
  module SuspRec = SuspensionRec

  open SuspensionRec public using () renaming (f to Suspension-rec)
  Susp-rec = Suspension-rec

  module SuspensionRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = suspension-span A} (λ _ → n) (λ _ → s) p
  module SuspRecType = SuspensionRecType

suspension-⊙span : ∀ {i} → Ptd i → ⊙Span
suspension-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp (A , _) = ⊙[ Suspension A , north ]


σloop : ∀ {i} (X : Ptd i) → fst X → north' (fst X) == north' (fst X)
σloop (_ , x₀) x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (snd X) == idp
σloop-pt {X = (_ , x₀)} = !-inv-r (merid x₀)


module SuspFlip {i} {A : Type i} = SuspensionRec
  (south' A) north (! ∘ merid)

Susp-flip : ∀ {i} {A : Type i} → Suspension A → Suspension A
Susp-flip = SuspFlip.f

⊙Susp-flip : ∀ {i} (X : Ptd i) → ⊙Susp X ⊙→ ⊙Susp X
⊙Susp-flip X = (Susp-flip , ! (merid (snd X)))

Susp-flip-equiv : ∀ {i} {A : Type i} → Suspension A ≃ Suspension A
Susp-flip-equiv {A = A} = Pushout-flip-equiv (suspension-span A)

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspensionRec north south (merid ∘ f)

  Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Suspension A → Suspension B)
  Susp-fmap = SuspFmap.f

  ⊙Susp-fmap : {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙Susp X ⊙→ ⊙Susp Y
  ⊙Susp-fmap (f , fpt) = (Susp-fmap f , idp)

module _ {i} where

  Susp-fmap-idf : (A : Type i) → ∀ a → Susp-fmap (idf A) a == a
  Susp-fmap-idf A = Suspension-elim idp idp $ λ a →
    ↓-='-in (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙Susp-fmap-idf : (X : Ptd i)
    → ⊙Susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙Susp-fmap-idf X = ⊙λ= (Susp-fmap-idf (fst X)) idp

module _ {i j} where

  Susp-fmap-cst : {A : Type i} {B : Type j} (b : B)
    (a : Suspension A) → Susp-fmap (cst b) a == north
  Susp-fmap-cst b = Suspension-elim idp (! (merid b)) $ (λ a →
    ↓-app=cst-from-square $ SuspFmap.merid-β (cst b) a ∙v⊡ tr-square _)

  ⊙Susp-fmap-cst : {X : Ptd i} {Y : Ptd j}
    → ⊙Susp-fmap (⊙cst {X = X} {Y = Y}) == ⊙cst
  ⊙Susp-fmap-cst = ⊙λ= (Susp-fmap-cst _) idp

  Susp-flip-fmap : {A : Type i} {B : Type j} (f : A → B)
    → ∀ σ → Susp-flip (Susp-fmap f σ) == Susp-fmap f (Susp-flip σ)
  Susp-flip-fmap f = Suspension-elim idp idp $ λ y → ↓-='-in $
    ap-∘ (Susp-fmap f) Susp-flip (merid y)
    ∙ ap (ap (Susp-fmap f)) (SuspFlip.merid-β y)
    ∙ ap-! (Susp-fmap f) (merid y)
    ∙ ap ! (SuspFmap.merid-β f y)
    ∙ ! (SuspFlip.merid-β (f y))
    ∙ ! (ap (ap Susp-flip) (SuspFmap.merid-β f y))
    ∙ ∘-ap Susp-flip (Susp-fmap f) (merid y)

module _ {i j k} where

  Susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
    (σ : Suspension A) → Susp-fmap (g ∘ f) σ == Susp-fmap g (Susp-fmap f σ)
  Susp-fmap-∘ g f = Suspension-elim
    idp
    idp
    (λ a → ↓-='-in $
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

  module ExtractGlue = PushoutRec {d = s} {D = Suspension (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  extract-glue = ExtractGlue.f

  module _ {x₀ : Span.A s} where

    ⊙extract-glue : (Pushout s , left x₀) ⊙→ (Suspension (Span.C s) , north)
    ⊙extract-glue = (extract-glue , idp)

module _ {i j} {A : Type i} {B : Type j} where

  Susp-emap : A ≃ B → Suspension A ≃ Suspension B
  Susp-emap eq = equiv to from to-from from-to where
    module To = SuspensionRec north south (λ a → merid (–> eq a))
    module From = SuspensionRec north south (λ b → merid (<– eq b))

    to : Suspension A → Suspension B
    to = To.f

    from : Suspension B → Suspension A
    from = From.f

    to-from : ∀ b → to (from b) == b
    to-from = Suspension-elim idp idp to-from-merid where
      to-from-merid : ∀ b → idp == idp [ (λ b → to (from b) == b) ↓ merid b ]
      to-from-merid b = ↓-app=idf-in $
        idp ∙' merid b
          =⟨ ∙'-unit-l (merid b) ⟩
        merid b
          =⟨ ! $ <–-inv-r eq b |in-ctx merid ⟩
        merid (–> eq (<– eq b))
          =⟨ ! $ To.merid-β (<– eq b) ⟩
        ap to (merid (<– eq b))
          =⟨ ! $ From.merid-β b |in-ctx ap To.f ⟩
        ap to (ap from (merid b))
          =⟨ ! $ ap-∘ to from (merid b) ⟩
        ap (to ∘ from) (merid b)
          =⟨ ! $ ∙-unit-r (ap (to ∘ from) (merid b)) ⟩
        ap (to ∘ from) (merid b) ∙ idp
          =∎

    from-to : ∀ a → from (to a) == a
    from-to = Suspension-elim idp idp from-to-merid where
      from-to-merid : ∀ a → idp == idp [ (λ a → from (to a) == a) ↓ merid a ]
      from-to-merid a = ↓-app=idf-in $
        idp ∙' merid a
          =⟨ ∙'-unit-l (merid a) ⟩
        merid a
          =⟨ ! $ <–-inv-l eq a |in-ctx merid ⟩
        merid (<– eq (–> eq a))
          =⟨ ! $ From.merid-β (–> eq a) ⟩
        ap from (merid (–> eq a))
          =⟨ ! $ To.merid-β a |in-ctx ap From.f ⟩
        ap from (ap to (merid a))
          =⟨ ! $ ap-∘ from to (merid a) ⟩
        ap (from ∘ to) (merid a)
          =⟨ ! $ ∙-unit-r (ap (from ∘ to) (merid a)) ⟩
        ap (from ∘ to) (merid a) ∙ idp
          =∎

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙Susp-emap : X ⊙≃ Y → ⊙Susp X ⊙≃ ⊙Susp Y
  ⊙Susp-emap ⊙eq = ≃-to-⊙≃ (Susp-emap (⊙≃-to-≃ ⊙eq)) idp

{- Interaction with [Lift] -}
module _ {i j} (X : Type i) where

  Susp-Lift-econv : Suspension (Lift {j = j} X) ≃ Lift {j = j} (Suspension X)
  Susp-Lift-econv = lift-equiv ∘e Susp-emap lower-equiv

  Susp-Lift-conv : Suspension (Lift {j = j} X) == Lift {j = j} (Suspension X)
  Susp-Lift-conv = ua Susp-Lift-econv

module _ {i j} (X : Ptd i) where

  ⊙Susp-Lift-econv : ⊙Susp (⊙Lift {j = j} X) ⊙≃ ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-Lift-econv = ⊙lift-equiv {j = j} ⊙∘e ⊙Susp-emap {X = ⊙Lift {j = j} X} {Y = X} ⊙lower-equiv

  ⊙Susp-Lift-conv : ⊙Susp (⊙Lift {j = j} X) == ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-Lift-conv = ⊙ua ⊙Susp-Lift-econv
