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
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.Lift
open import lib.cubical.Cube
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

    private
      module P = PushoutElim (λ _ → n) (λ _ → s) p

    abstract
      f : Π (Susp A) P
      f = P.f

      north-β : f north ↦ n
      north-β = P.left-β unit
      {-# REWRITE north-β #-}

      south-β : f south ↦ s
      south-β = P.right-β unit
      {-# REWRITE south-β #-}

      merid-β : ∀ a → apd f (merid a) == p a
      merid-β = P.glue-β

  open SuspElim public using () renaming (f to Susp-elim)

  module SuspRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    private
      module P = PushoutRec {d = susp-span A} (λ _ → n) (λ _ → s) p

    abstract
      f : Susp A → C
      f = P.f

      north-β : f north ↦ n
      north-β = P.left-β unit
      {-# REWRITE north-β #-}

      south-β : f south ↦ s
      south-β = P.right-β unit
      {-# REWRITE south-β #-}

      merid-β : ∀ a → ap f (merid a) == p a
      merid-β = P.glue-β

  open SuspRec public using () renaming (f to Susp-rec)

  module SuspRecType {j} (n s : Type j) (p : A → n ≃ s)
    = PushoutRecType {d = susp-span A} (λ _ → n) (λ _ → s) p

module SuspPathElim
  {i} {j} {A : Type i} {B : Type j}
  (f g : Susp A → B)
  (n : f north == g north)
  (s : f south == g south)
  (m : ∀ a → Square n (ap f (merid a)) (ap g (merid a)) s)
  where

  private
    module M =
      SuspElim
        {P = λ sa → f sa == g sa}
        n
        s
        (λ a → ↓-='-from-square (m a))

  open M public

  merid-square-β : ∀ a → natural-square M.f (merid a) == m a
  merid-square-β a = natural-square-β M.f (merid a) (M.merid-β a)

module SuspDoublePathElim
  {i} {j} {k} {A : Type i} {B : Type j} {C : Type k}
  (f g : Susp A → Susp B → C)
  (n-n : f north north == g north north)
  (n-s : f north south == g north south)
  (s-n : f south north == g south north)
  (s-s : f south south == g south south)
  (n-m : ∀ b → Square n-n (ap (f north) (merid b)) (ap (g north) (merid b)) n-s)
  (s-m : ∀ b → Square s-n (ap (f south) (merid b)) (ap (g south) (merid b)) s-s)
  (m-n : ∀ a → Square n-n (ap (λ sa → f sa north) (merid a)) (ap (λ sa → g sa north) (merid a)) s-n)
  (m-s : ∀ a → Square n-s (ap (λ sa → f sa south) (merid a)) (ap (λ sa → g sa south) (merid a)) s-s)
  (m-m : ∀ a b →
    Cube (m-n a)
         (m-s a)
         (n-m b)
         (natural-square (λ sb → ap (λ sa → f sa sb) (merid a)) (merid b))
         (natural-square (λ sb → ap (λ sa → g sa sb) (merid a)) (merid b))
         (s-m b))
  where

  private
    module N =
      SuspElim
        {P = λ sb → f north sb == g north sb}
        n-n
        n-s
        (λ b → ↓-='-from-square (n-m b))

    n-natural-square : ∀ (b : B) →
      natural-square N.f (merid b) == n-m b
    n-natural-square b = natural-square-β N.f (merid b) (N.merid-β b)

    module S =
      SuspElim
        {P = λ sb → f south sb == g south sb}
        s-n
        s-s
        (λ b → ↓-='-from-square (s-m b))

    s-natural-square : ∀ (b : B) →
      natural-square S.f (merid b) == s-m b
    s-natural-square b = natural-square-β S.f (merid b) (S.merid-β b)

    module M (sb : Susp B) =
      SuspElim {A = A}
        {P = λ sa → f sa sb == g sa sb}
        (N.f sb)
        (S.f sb)
        (λ a → Susp-elim
          {P = λ sb → N.f sb == S.f sb [ (λ sa → f sa sb == g sa sb) ↓ merid a ]}
          (↓-='-from-square (m-n a))
          (↓-='-from-square (m-s a))
          (λ b → ap↓ ↓-='-from-square $
            cube-to-↓-square $
            cube-shift-back (! (n-natural-square b)) $
            cube-shift-front (! (s-natural-square b)) $
            m-m a b)
          sb)

  abstract
    p : ∀ sa sb → f sa sb == g sa sb
    p sa sb = M.f sb sa

    north-north-β : p north north ↦ n-n
    north-north-β = N.north-β
    {-# REWRITE north-north-β #-}

    north-south-β : p north south ↦ n-s
    north-south-β = N.south-β
    {-# REWRITE north-south-β #-}

    south-north-β : p south north ↦ s-n
    south-north-β = S.north-β
    {-# REWRITE south-north-β #-}

    south-south-β : p south south ↦ s-s
    south-south-β = S.south-β
    {-# REWRITE south-south-β #-}

    north-merid-β : ∀ b → apd (p north) (merid b) == ↓-='-from-square (n-m b)
    north-merid-β = N.merid-β

    north-merid-square-β : ∀ b → natural-square (p north) (merid b) == n-m b
    north-merid-square-β b = natural-square-β (p north) (merid b) (north-merid-β b)

    south-merid-β : ∀ b → apd (p south) (merid b) == ↓-='-from-square (s-m b)
    south-merid-β = S.merid-β

    south-merid-square-β : ∀ b → natural-square (p south) (merid b) == s-m b
    south-merid-square-β b = natural-square-β (p south) (merid b) (south-merid-β b)

    merid-north-β : ∀ a → apd (λ sa → p sa north) (merid a) == ↓-='-from-square (m-n a)
    merid-north-β = M.merid-β north

    merid-north-square-β : ∀ a → natural-square (λ sa → p sa north) (merid a) == m-n a
    merid-north-square-β a =
      natural-square-β (λ sa → p sa north) (merid a) (merid-north-β a)

    merid-south-β : ∀ a → apd (λ sa → p sa south) (merid a) == ↓-='-from-square (m-s a)
    merid-south-β = M.merid-β south

    merid-south-square-β : ∀ a → natural-square (λ sa → p sa south) (merid a) == m-s a
    merid-south-square-β a =
      natural-square-β (λ sa → p sa south) (merid a) (merid-south-β a)

susp-⊙span : ∀ {i} → Ptd i → ⊙Span
susp-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Type i → Ptd i
⊙Susp A = ⊙[ Susp A , north ]


σloop : ∀ {i} (X : Ptd i) → de⊙ X → north' (de⊙ X) == north' (de⊙ X)
σloop ⊙[ _ , x₀ ] x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (pt X) == idp
σloop-pt {X = ⊙[ _ , x₀ ]} = !-inv-r (merid x₀)

⊙σloop : ∀ {i} (X : Ptd i) → X ⊙→ ⊙[ north' (de⊙ X) == north' (de⊙ X) , idp ]
⊙σloop X = σloop X , σloop-pt


module SuspFlip {i} {A : Type i} = SuspRec
  (south' A) north (! ∘ merid)

Susp-flip : ∀ {i} {A : Type i} → Susp A → Susp A
Susp-flip = SuspFlip.f

⊙Susp-flip : ∀ {i} (X : Ptd i) → ⊙Susp (de⊙ X) ⊙→ ⊙Susp (de⊙ X)
⊙Susp-flip X = (Susp-flip , ! (merid (pt X)))

Susp-flip-flip : ∀ {i} {A : Type i} (sa : Susp A)
  → Susp-flip (Susp-flip sa) == sa
Susp-flip-flip =
  Susp-elim
    idp
    idp $ λ a → ↓-='-in' $
  ap (λ z → z) (merid a)
    =⟨ ap-idf (merid a) ⟩
  merid a
    =⟨ ! (!-! (merid a)) ⟩
  ! (! (merid a))
    =⟨ ap ! (! (SuspFlip.merid-β a)) ⟩
  ! (ap Susp-flip (merid a))
    =⟨ !-ap Susp-flip (merid a) ⟩
  ap Susp-flip (! (merid a))
    =⟨ ap (ap Susp-flip) (! (SuspFlip.merid-β a)) ⟩
  ap Susp-flip (ap Susp-flip (merid a))
    =⟨ ∘-ap Susp-flip Susp-flip (merid a) ⟩
  ap (Susp-flip ∘ Susp-flip) (merid a) =∎

Susp-flip-equiv : ∀ {i} {A : Type i} → Susp A ≃ Susp A
Susp-flip-equiv {A = A} =
  equiv Susp-flip Susp-flip Susp-flip-flip Susp-flip-flip

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspRec north south (merid ∘ f)

  Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Susp A → Susp B)
  Susp-fmap = SuspFmap.f

  ⊙Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → ⊙Susp A ⊙→ ⊙Susp B
  ⊙Susp-fmap f = (Susp-fmap f , idp)

module _ {i} (A : Type i) where

  Susp-fmap-idf : ∀ a → Susp-fmap (idf A) a == a
  Susp-fmap-idf = Susp-elim idp idp $ λ a →
    ↓-='-in' (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙Susp-fmap-idf : ⊙Susp-fmap (idf A) == ⊙idf (⊙Susp A)
  ⊙Susp-fmap-idf = ⊙λ=' Susp-fmap-idf idp

Susp-fmap-coe : ∀ {i} {A B : Type i} (p : A == B)
  → ∀ sa → Susp-fmap (coe p) sa == transport Susp p sa
Susp-fmap-coe {i} {A} {.A} p@idp = Susp-fmap-idf A

module _ {i} {A : Type i} where

  Susp-fmap-cst : ∀ {j} {B : Type j} (b : B)
    (a : Susp A) → Susp-fmap (cst b) a == north
  Susp-fmap-cst b = Susp-elim idp (! (merid b)) $ (λ a →
    ↓-app=cst-from-square $ SuspFmap.merid-β (cst b) a ∙v⊡ tr-square _)

  ⊙Susp-fmap-cst : ∀ {j} {Y : Ptd j}
    → ⊙Susp-fmap {A = A} (λ _ → pt Y) == ⊙cst
  ⊙Susp-fmap-cst = ⊙λ=' (Susp-fmap-cst _) idp

  Susp-flip-natural : ∀ {j} {B : Type j} (f : A → B)
    → ∀ σ → Susp-flip (Susp-fmap f σ) == Susp-fmap f (Susp-flip σ)
  Susp-flip-natural f = Susp-elim idp idp $ λ y → ↓-='-in' $
    ap-∘ (Susp-fmap f) Susp-flip (merid y)
    ∙ ap (ap (Susp-fmap f)) (SuspFlip.merid-β y)
    ∙ ap-! (Susp-fmap f) (merid y)
    ∙ ap ! (SuspFmap.merid-β f y)
    ∙ ! (SuspFlip.merid-β (f y))
    ∙ ! (ap (ap Susp-flip) (SuspFmap.merid-β f y))
    ∙ ∘-ap Susp-flip (Susp-fmap f) (merid y)

  Susp-fmap-flip : (x : Susp (Susp A))
    → Susp-fmap Susp-flip x == Susp-flip x
  Susp-fmap-flip =
    Susp-elim
      {P = λ x → Susp-fmap Susp-flip x == Susp-flip x}
      (merid north)
      (! (merid south)) $ λ y →
    ↓-='-in-=ₛ $
    merid north ◃∙
    ap Susp-flip (merid y) ◃∎
      =ₛ₁⟨ 1 & 1 & SuspFlip.merid-β y ⟩
    merid north ◃∙
    ! (merid y) ◃∎
      =ₛ⟨ =ₛ-in {t = merid (Susp-flip y) ◃∙ ! (merid south) ◃∎} $
          Susp-elim
             {P = λ y → merid north ∙ ! (merid y) == merid (Susp-flip y) ∙ ! (merid south)}
             (!-inv-r (merid north) ∙ ! (!-inv-r (merid south)))
             idp
             (λ a → ↓-='-in-=ₛ $
               (!-inv-r (merid north) ∙ ! (!-inv-r (merid south))) ◃∙
               ap (λ z → merid (Susp-flip z) ∙ ! (merid south)) (merid a) ◃∎
                 =ₛ⟨ 0 & 1 & expand (!-inv-r (merid north) ◃∙ ! (!-inv-r (merid south)) ◃∎) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z → merid (Susp-flip z) ∙ ! (merid south)) (merid a) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap-∘ (λ z' → merid z' ∙ ! (merid south)) Susp-flip (merid a) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z' → merid z' ∙ ! (merid south)) (ap Susp-flip (merid a)) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap (ap (λ z' → merid z' ∙ ! (merid south)))
                                 (SuspFlip.merid-β a) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (λ z' → merid z' ∙ ! (merid south)) (! (merid a)) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap-∘ (_∙ ! (merid south)) merid (! (merid a)) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (_∙ ! (merid south)) (ap merid (! (merid a))) ◃∎
                 =ₛ₁⟨ 2 & 1 & ap (ap (_∙ ! (merid south))) (ap-! merid (merid a)) ⟩
               !-inv-r (merid north) ◃∙
               ! (!-inv-r (merid south)) ◃∙
               ap (_∙ ! (merid south)) (! (ap merid (merid a))) ◃∎
                 =ₛ⟨ pre-rotate-out $ coh-helper (ap merid (merid a)) ⟩
               ap (λ q → merid north ∙ ! q) (ap merid (merid a)) ◃∎
                 =ₛ₁⟨ ∘-ap (λ q → merid north ∙ ! q) merid (merid a) ⟩
               ap (λ z → merid north ∙ ! (merid z)) (glue a) ◃∎
                 =ₛ⟨ 1 & 0 & contract ⟩
               ap (λ z → merid north ∙ ! (merid z)) (glue a) ◃∙ idp ◃∎ ∎ₛ )
             y ⟩
    merid (Susp-flip y) ◃∙
    ! (merid south) ◃∎
      =ₛ₁⟨ 0 & 1 & ! (SuspFmap.merid-β Susp-flip y) ⟩
    ap (Susp-fmap Susp-flip) (merid y) ◃∙
    ! (merid south) ◃∎ ∎ₛ
    where
      coh-helper : ∀ {j} {B : Type j}
        {b-north b-south : B}
        {merid₁ merid₂ : b-north == b-south}
        (p : merid₁ == merid₂)
        → ! (!-inv-r merid₂) ◃∙
          ap (_∙ ! merid₂) (! p) ◃∎
          =ₛ
          ! (!-inv-r merid₁) ◃∙
          ap (λ q → merid₁ ∙ ! q) p ◃∎
      coh-helper {merid₁ = idp} {merid₂ = .idp} idp =
        =ₛ-in idp

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

  ⊙Susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k}
    (g : B → C) (f : A → B)
    → ⊙Susp-fmap (g ∘ f) == ⊙Susp-fmap g ⊙∘ ⊙Susp-fmap f
  ⊙Susp-fmap-∘ g f = ⊙λ=' (Susp-fmap-∘ g f) idp


{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtractGlue = PushoutRec {d = s} {D = Susp (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  extract-glue = ExtractGlue.f

  module _ {x₀ : Span.A s} where

    ⊙extract-glue : ⊙[ Pushout s , left x₀ ] ⊙→ ⊙[ Susp (Span.C s) , north ]
    ⊙extract-glue = extract-glue , idp

module _ {i j} {A : Type i} {B : Type j} (eq : A ≃ B) where

  Susp-emap : Susp A ≃ Susp B
  Susp-emap =
    equiv
      (Susp-fmap (–> eq))
      (Susp-fmap (<– eq))
      (λ sb →
        Susp-fmap (–> eq) (Susp-fmap (<– eq) sb)
          =⟨ ! (Susp-fmap-∘ (–> eq) (<– eq) sb) ⟩
        Susp-fmap ((–> eq) ∘ (<– eq)) sb
          =⟨ ap (λ f → Susp-fmap f sb) (λ= (<–-inv-r eq)) ⟩
        Susp-fmap (idf B) sb
          =⟨ Susp-fmap-idf _ sb ⟩
        sb =∎)
      (λ sa →
        Susp-fmap (<– eq) (Susp-fmap (–> eq) sa)
          =⟨ ! (Susp-fmap-∘ (<– eq) (–> eq) sa) ⟩
        Susp-fmap ((<– eq) ∘ (–> eq)) sa
          =⟨ ap (λ f → Susp-fmap f sa) (λ= (<–-inv-l eq)) ⟩
        Susp-fmap (idf A) sa
          =⟨ Susp-fmap-idf _ sa ⟩
        sa =∎)

  private
    -- This is to make sure that we did not screw up [Susp-emap].
    test₀ : fst Susp-emap == Susp-fmap (fst eq)
    test₀ = idp

module _ {i j} {A : Type i} {B : Type j} where

  ⊙Susp-emap : A ≃ B → ⊙Susp A ⊙≃ ⊙Susp B
  ⊙Susp-emap eq = ≃-to-⊙≃ (Susp-emap eq) idp

{- Interaction with [Lift] -}
module _ {i j} (A : Type i) where

  Susp-Lift-econv : Susp (Lift {j = j} A) ≃ Lift {j = j} (Susp A)
  Susp-Lift-econv = lift-equiv ∘e Susp-emap lower-equiv

  Susp-Lift-conv : Susp (Lift {j = j} A) == Lift {j = j} (Susp A)
  Susp-Lift-conv = ua Susp-Lift-econv

module _ {i j} (A : Type i) where

  ⊙Susp-Lift-econv : ⊙Susp (Lift {j = j} A) ⊙≃ ⊙Lift {j = j} (⊙Susp A)
  ⊙Susp-Lift-econv = ⊙lift-equiv {j = j} ⊙∘e ⊙Susp-emap {A = Lift {j = j} A} {B = A} lower-equiv

  ⊙Susp-Lift-conv : ⊙Susp (Lift {j = j} A) == ⊙Lift {j = j} (⊙Susp A)
  ⊙Susp-Lift-conv = ⊙ua ⊙Susp-Lift-econv

module _ {i} (A : Type i) (m : ℕ₋₂) where

  module SuspTruncSwap =
    SuspRec
      {C = Trunc (S m) (Susp A)}
      [ north ]
      [ south ]
      (Trunc-rec
        {B = [ north ] == [ south ]}
        {{has-level-apply (Trunc-level {n = S m}) [ north ] [ south ]}}
        (λ x → ap [_] (merid x)))

  Susp-Trunc-swap : Susp (Trunc m A) → Trunc (S m) (Susp A)
  Susp-Trunc-swap = SuspTruncSwap.f

  Susp-Trunc-swap-Susp-fmap-trunc : ∀ (s : Susp A) →
    Susp-Trunc-swap (Susp-fmap [_] s) == [ s ]
  Susp-Trunc-swap-Susp-fmap-trunc =
    Susp-elim
      idp
      idp $
    λ a → ↓-='-in' $ ! $
    ap (Susp-Trunc-swap ∘ Susp-fmap [_]) (merid a)
      =⟨ ap-∘ Susp-Trunc-swap (Susp-fmap [_]) (merid a) ⟩
    ap Susp-Trunc-swap (ap (Susp-fmap [_]) (merid a))
      =⟨ ap (ap Susp-Trunc-swap) (SuspFmap.merid-β [_] a) ⟩
    ap Susp-Trunc-swap (merid [ a ])
      =⟨ SuspTruncSwap.merid-β [ a ] ⟩
    ap [_] (merid a) =∎

  Susp-Trunc-swap-Susp-flip :
    Susp-Trunc-swap ∘ Susp-flip ∼
    Trunc-fmap Susp-flip ∘ Susp-Trunc-swap
  Susp-Trunc-swap-Susp-flip =
    Susp-elim
      idp
      idp $
    Trunc-elim {{λ t → ↓-level (=-preserves-level Trunc-level)}} $ λ a →
    ↓-='-in' $
    ap (Trunc-fmap Susp-flip ∘ Susp-Trunc-swap) (merid [ a ])
      =⟨ ap-∘ (Trunc-fmap Susp-flip) Susp-Trunc-swap (merid [ a ]) ⟩
    ap (Trunc-fmap Susp-flip) (ap Susp-Trunc-swap (merid [ a ]))
      =⟨ ap (ap (Trunc-fmap Susp-flip)) (SuspTruncSwap.merid-β [ a ]) ⟩
    ap (Trunc-fmap Susp-flip) (ap [_] (merid a))
      =⟨ ∘-ap (Trunc-fmap Susp-flip) [_] (merid a) ⟩
    ap ([_] ∘ Susp-flip) (merid a)
      =⟨ ap-∘ [_] Susp-flip (merid a) ⟩
    ap [_] (ap Susp-flip (merid a))
      =⟨ ap (ap [_]) (SuspFlip.merid-β a) ⟩
    ap [_] (! (merid a))
      =⟨ ap-! [_] (merid a) ⟩
    ! (ap [_] (merid a))
      =⟨ ap ! (! (SuspTruncSwap.merid-β [ a ])) ⟩
    ! (ap Susp-Trunc-swap (merid [ a ]))
      =⟨ !-ap Susp-Trunc-swap (merid [ a ]) ⟩
    ap Susp-Trunc-swap (! (merid [ a ]))
      =⟨ ap (ap Susp-Trunc-swap) (! (SuspFlip.merid-β [ a ])) ⟩
    ap Susp-Trunc-swap (ap Susp-flip (merid [ a ]))
      =⟨ ∘-ap Susp-Trunc-swap Susp-flip (merid [ a ]) ⟩
    ap (Susp-Trunc-swap ∘ Susp-flip) (merid [ a ]) =∎

abstract
  Susp-Trunc-swap-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B) (m : ℕ₋₂)
    → Susp-Trunc-swap B m ∘ Susp-fmap (Trunc-fmap f) ∼
      Trunc-fmap (Susp-fmap f) ∘ Susp-Trunc-swap A m
  Susp-Trunc-swap-natural {A = A} {B} f m =
    Susp-elim
      idp
      idp $
    Trunc-elim {{λ t → ↓-level (=-preserves-level Trunc-level)}} $ λ s →
    ↓-='-in' $
    ap (Trunc-fmap (Susp-fmap f) ∘ Susp-Trunc-swap A m) (merid [ s ])
      =⟨ ap-∘ (Trunc-fmap (Susp-fmap f)) (Susp-Trunc-swap A m) (merid [ s ]) ⟩
    ap (Trunc-fmap (Susp-fmap f)) (ap (Susp-Trunc-swap A m) (merid [ s ]))
      =⟨ ap (ap (Trunc-fmap (Susp-fmap f))) (SuspTruncSwap.merid-β A m [ s ]) ⟩
    ap (Trunc-fmap (Susp-fmap f)) (ap [_] (merid s))
      =⟨ ∘-ap (Trunc-fmap (Susp-fmap f)) [_] (merid s) ⟩
    ap ([_] ∘ Susp-fmap f) (merid s)
      =⟨ ap-∘ [_] (Susp-fmap f) (merid s) ⟩
    ap [_] (ap (Susp-fmap f) (merid s))
      =⟨ ap (ap [_]) (SuspFmap.merid-β f s) ⟩
    ap [_] (merid (f s))
      =⟨ ! (SuspTruncSwap.merid-β B m [ f s ]) ⟩
    ap (Susp-Trunc-swap B m) (merid [ f s ])
      =⟨ ap (ap (Susp-Trunc-swap B m)) (! (SuspFmap.merid-β (Trunc-fmap f) [ s ])) ⟩
    ap (Susp-Trunc-swap B m) (ap (Susp-fmap (Trunc-fmap f)) (merid [ s ]))
      =⟨ ∘-ap (Susp-Trunc-swap B m) (Susp-fmap (Trunc-fmap f)) (merid [ s ]) ⟩
    ap (Susp-Trunc-swap B m ∘ Susp-fmap (Trunc-fmap f)) (merid [ s ]) =∎

⊙Susp-Trunc-swap : ∀ {i} (A : Type i) (m : ℕ₋₂)
  → ⊙Susp (Trunc m A) ⊙→ ⊙Trunc (S m) (⊙Susp A)
⊙Susp-Trunc-swap A m = Susp-Trunc-swap A m , idp

{- Suspension of an n-connected space is n+1-connected -}
abstract
  Susp-conn : ∀ {i} {A : Type i} {n : ℕ₋₂}
    → is-connected n A → is-connected (S n) (Susp A)
  Susp-conn {A = A} {n = n} cA = has-level-in
    ([ north ] ,
     Trunc-elim
       (Susp-elim
         idp
         (Trunc-rec (λ a → ap [_] (merid a))
                    (contr-center cA))
         (λ x → Trunc-elim
            {P = λ y → idp ==
              Trunc-rec (λ a → ap [_] (merid a)) y
              [ (λ z → [ north ] == [ z ]) ↓ (merid x) ]}
            {{λ _ → ↓-preserves-level ⟨⟩}}
            (λ x' → ↓-cst=app-in (∙'-unit-l _ ∙ mers-eq n x x'))
            (contr-center cA))))
    where
    instance _ = cA

    mers-eq : ∀ {i} {A : Type i} (n : ℕ₋₂)
      {{_ : is-connected n A}} → (x x' : A)
      → ap ([_] {n = S n}) (merid x)
        == Trunc-rec {{has-level-apply (Trunc-level {n = S n}) _ _}} (λ a → ap [_] (merid a)) [ x' ]
    mers-eq ⟨-2⟩ x x' = contr-has-all-paths _ _
    mers-eq {A = A} (S n) x x' =
      conn-extend (pointed-conn-out A x)
        (λ y → ((ap [_] (merid x) == ap [_] (merid y)) ,
                has-level-apply (has-level-apply (Trunc-level {n = S (S n)}) _ _) _ _))
        (λ _ → idp) x'
