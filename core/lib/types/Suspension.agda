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

  open SuspensionElim public using () renaming (f to Suspension-elim)

  module SuspensionRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    open module P = PushoutRec {d = suspension-span A} (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspensionRec public using () renaming (f to Suspension-rec)

  module SuspensionRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = suspension-span A} (λ _ → n) (λ _ → s) p

suspension-⊙span : ∀ {i} → Ptd i → ⊙Span
suspension-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp (A , _) = ⊙[ Suspension A , north ]


σloop : ∀ {i} (X : Ptd i) → fst X → north' (fst X) == north' (fst X)
σloop (_ , x₀) x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (snd X) == idp
σloop-pt {X = (_ , x₀)} = !-inv-r (merid x₀)


module FlipSusp {i} {A : Type i} = SuspensionRec
  (south' A) north (! ∘ merid)

flip-susp : ∀ {i} {A : Type i} → Suspension A → Suspension A
flip-susp = FlipSusp.f

⊙flip-susp : ∀ {i} (X : Ptd i) → fst (⊙Susp X ⊙→ ⊙Susp X)
⊙flip-susp X = (flip-susp , ! (merid (snd X)))

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspensionRec north south (merid ∘ f)

  susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Suspension A → Suspension B)
  susp-fmap = SuspFmap.f

  ⊙susp-fmap : {X : Ptd i} {Y : Ptd j} (f : fst (X ⊙→ Y))
    → fst (⊙Susp X ⊙→ ⊙Susp Y)
  ⊙susp-fmap (f , fpt) = (susp-fmap f , idp)

module _ {i} where

  susp-fmap-idf : (A : Type i) → ∀ a → susp-fmap (idf A) a == a
  susp-fmap-idf A = Suspension-elim idp idp $ λ a →
    ↓-='-in (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙susp-fmap-idf : (X : Ptd i)
    → ⊙susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙susp-fmap-idf X = ⊙λ= (susp-fmap-idf (fst X)) idp

module _ {i j} where

  susp-fmap-cst : {A : Type i} {B : Type j} (b : B)
    (a : Suspension A) → susp-fmap (cst b) a == north
  susp-fmap-cst b = Suspension-elim idp (! (merid b)) $ (λ a →
    ↓-app=cst-from-square $ SuspFmap.merid-β (cst b) a ∙v⊡ tr-square _)

  ⊙susp-fmap-cst : {X : Ptd i} {Y : Ptd j}
    → ⊙susp-fmap (⊙cst {X = X} {Y = Y}) == ⊙cst
  ⊙susp-fmap-cst = ⊙λ= (susp-fmap-cst _) idp

module _ {i j k} where

  susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
    (σ : Suspension A) → susp-fmap (g ∘ f) σ == susp-fmap g (susp-fmap f σ)
  susp-fmap-∘ g f = Suspension-elim
    idp
    idp
    (λ a → ↓-='-in $
      ap-∘ (susp-fmap g) (susp-fmap f) (merid a)
      ∙ ap (ap (susp-fmap g)) (SuspFmap.merid-β f a)
      ∙ SuspFmap.merid-β g (f a)
      ∙ ! (SuspFmap.merid-β (g ∘ f) a))

  ⊙susp-fmap-∘ : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
    (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
    → ⊙susp-fmap (g ⊙∘ f) == ⊙susp-fmap g ⊙∘ ⊙susp-fmap f
  ⊙susp-fmap-∘ g f = ⊙λ= (susp-fmap-∘ (fst g) (fst f)) idp


{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtGlue = PushoutRec {d = s} {D = Suspension (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  ext-glue = ExtGlue.f

  module _ {x₀ : Span.A s} where

    ⊙ext-glue :
      fst ((Pushout s , left x₀) ⊙→ (Suspension (Span.C s) , north))
    ⊙ext-glue = (ext-glue , idp)

module _ {i j} {A : Type i} {B : Type j} where

  Suspension-equiv : A ≃ B → Suspension A ≃ Suspension B
  Suspension-equiv eq = equiv to from to-from from-to where
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
          ∎

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
          ∎

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  ⊙Susp-equiv : X ⊙≃ Y → ⊙Susp X ⊙≃ ⊙Susp Y
  ⊙Susp-equiv ⊙eq = ⊙≃-in (Suspension-equiv (fst (⊙≃-out ⊙eq))) idp

{- Interaction with [Lift] -}
module _ {i j} (X : Type i) where

  Suspension-Lift-equiv : Suspension (Lift {j = j} X) ≃ Lift {j = j} (Suspension X)
  Suspension-Lift-equiv = lift-equiv ∘e Suspension-equiv lower-equiv

  Suspension-Lift-path : Suspension (Lift {j = j} X) == Lift {j = j} (Suspension X)
  Suspension-Lift-path = ua Suspension-Lift-equiv

module _ {i j} (X : Ptd i) where

  ⊙Susp-⊙Lift-equiv : ⊙Susp (⊙Lift {j = j} X) ⊙≃ ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-⊙Lift-equiv = ⊙lift-equiv {j = j} ⊙∘e ⊙Susp-equiv {X = ⊙Lift {j = j} X} {Y = X} ⊙lower-equiv

  ⊙Susp-⊙Lift-path : ⊙Susp (⊙Lift {j = j} X) == ⊙Lift {j = j} (⊙Susp X)
  ⊙Susp-⊙Lift-path = ⊙ua ⊙Susp-⊙Lift-equiv
