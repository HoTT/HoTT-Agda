{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Coproduct
open import lib.types.Paths
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.Sigma

module lib.types.Smash where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙∧-span : ⊙Span
  ⊙∧-span = ⊙span (X ⊙× Y) ⊙Bool (X ⊙⊔ Y)
    (⊔-rec (_, pt Y) (pt X ,_) , idp)
    (⊙⊔-fmap {Y = Y} ⊙cst ⊙cst)

  ∧-span : Span
  ∧-span = ⊙Span-to-Span ⊙∧-span

  abstract
    _∧_ : Type (lmax i j)
    _∧_ = Pushout ∧-span
  Smash = _∧_

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  abstract
    smin : de⊙ X → de⊙ Y → Smash X Y
    smin x y = left (x , y)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  _⊙∧_ = ptd (X ∧ Y) (smin (pt X) (pt Y))
  ⊙Smash = _⊙∧_

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  abstract

    smbasel : Smash X Y
    smbasel = right true

    smbaser : Smash X Y
    smbaser = right false

    smgluel : (x : de⊙ X) → smin x (pt Y) == smbasel
    smgluel x = glue (inl x)

    smgluer : (y : de⊙ Y) → smin (pt X) y == smbaser
    smgluer y = glue (inr y)

  ∧-norm-l-seq : (x : de⊙ X) → smin x (pt Y) =-= smin (pt X) (pt Y)
  ∧-norm-l-seq x = smgluel x ◃∙ ! (smgluel (pt X)) ◃∎

  ∧-norm-l : (x : de⊙ X) → smin x (pt Y) == smin (pt X) (pt Y)
  ∧-norm-l x = ↯ (∧-norm-l-seq x)

  ∧-norm-r-seq : (y : de⊙ Y) → smin (pt X) y =-= smin (pt X) (pt Y)
  ∧-norm-r-seq y = smgluer y ◃∙ ! (smgluer (pt Y)) ◃∎

  ∧-norm-r : (y : de⊙ Y) → smin (pt X) y == smin (pt X) (pt Y)
  ∧-norm-r y = ↯ (∧-norm-r-seq y)

  ∧-⊙inl : de⊙ Y → X ⊙→ ⊙Smash X Y
  ∧-⊙inl y = (λ x → smin x y) , smgluer y ∙ ! (smgluer (pt Y))

  ∧-⊙inr : de⊙ X → Y ⊙→ ⊙Smash X Y
  ∧-⊙inr x = (λ y → smin x y) , smgluel x ∙ ! (smgluel (pt X))

  ∧-glue-lr : smbasel == smbaser
  ∧-glue-lr = ! (smgluel (pt X)) ∙ smgluer (pt Y)

  ap-smin-l : {a b : de⊙ X} (p : a == b)
    → ap (λ x → smin x (pt Y)) p == smgluel a ∙ ! (smgluel b)
  ap-smin-l = homotopy-to-cst-ap (λ x → smin x (pt Y)) smbasel smgluel

  ap-smin-r : {a b : de⊙ Y} (p : a == b)
    → ap (smin (pt X)) p == smgluer a ∙ ! (smgluer b)
  ap-smin-r = homotopy-to-cst-ap (λ y → smin (pt X) y) smbaser smgluer

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  module SmashElim {k} {P : Smash X Y → Type k}
    (smin* : (x : de⊙ X) (y : de⊙ Y) → P (smin x y))
    (smbasel* : P smbasel) (smbaser* : P smbaser)
    (smgluel* : (x : de⊙ X) → smin* x (pt Y) == smbasel* [ P ↓ smgluel x ])
    (smgluer* : (y : de⊙ Y) → smin* (pt X) y == smbaser* [ P ↓ smgluer y ]) where

    -- It would be better to encapsulate the repetition in the following definitions in a
    -- private module as follows. Unfortunately, this is not possible when the smash
    -- datatype is declared abstract.
    {-private
      module M = PushoutElim
        (uncurry smin*)
        (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*))
        (Coprod-elim smgluel* smgluer*)-}

    abstract
      f : (s : X ∧ Y) → P s
      f = PushoutElim.f (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*)

      smin-β : ∀ x y → f (smin x y) ↦ smin* x y
      smin-β x y = PushoutElim.left-β (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) (x , y)
      {-# REWRITE smin-β #-}

      smbasel-β : f smbasel ↦ smbasel*
      smbasel-β = PushoutElim.right-β (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) true
      {-# REWRITE smbasel-β #-}

      smbaser-β : f smbaser ↦ smbaser*
      smbaser-β = PushoutElim.right-β (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) false
      {-# REWRITE smbaser-β #-}

      smgluel-β : ∀ (x : de⊙ X) → apd f (smgluel x) == smgluel* x
      smgluel-β = PushoutElim.glue-β (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) ∘ inl

      smgluer-β : ∀ (y : de⊙ Y) → apd f (smgluer y) == smgluer* y
      smgluer-β = PushoutElim.glue-β (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) ∘ inr

  Smash-elim = SmashElim.f

  module SmashRec {k} {C : Type k}
    (smin* : (x : de⊙ X) (y : de⊙ Y) → C)
    (smbasel* smbaser* : C)
    (smgluel* : (x : de⊙ X) → smin* x (pt Y) == smbasel*)
    (smgluer* : (y : de⊙ Y) → smin* (pt X) y == smbaser*) where

    -- It would be better to encapsulate the repetition in the following definitions in a
    -- private module as follows. Unfortunately, this is not possible when the smash
    -- datatype is declared abstract.
    {-private
      module M = PushoutRec {d = ∧-span X Y}
        (uncurry smin*)
        (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*))
        (Coprod-elim smgluel* smgluer*)-}

    abstract
      f : X ∧ Y → C
      f = PushoutRec.f (uncurry smin*) (Coprod-elim (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*)

      smin-β : ∀ x y → f (smin x y) ↦ smin* x y
      smin-β x y = PushoutRec.left-β {d = ∧-span X Y} (uncurry smin*) (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) (x , y)
      {-# REWRITE smin-β #-}

      smbasel-β : f smbasel ↦ smbasel*
      smbasel-β = PushoutRec.right-β {d = ∧-span X Y} (uncurry smin*) (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) true
      {-# REWRITE smbasel-β #-}

      smbaser-β : f smbaser ↦ smbaser*
      smbaser-β = PushoutRec.right-β {d = ∧-span X Y} (uncurry smin*) (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) false
      {-# REWRITE smbaser-β #-}

      smgluel-β : ∀ (x : de⊙ X) → ap f (smgluel x) == smgluel* x
      smgluel-β = PushoutRec.glue-β (uncurry smin*) (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) ∘ inl

      smgluer-β : ∀ (y : de⊙ Y) → ap f (smgluer y) == smgluer* y
      smgluer-β = PushoutRec.glue-β (uncurry smin*) (Coprod-rec (λ _ → smbasel*) (λ _ → smbaser*)) (Coprod-elim smgluel* smgluer*) ∘ inr

  Smash-rec = SmashRec.f

  module SmashPathOverElim {k} {P : Smash X Y → Type k}
    (g₁ g₂ : (xy : Smash X Y) → P xy)
    (smin* : (x : de⊙ X) (y : de⊙ Y) → g₁ (smin x y) == g₂ (smin x y))
    (smbasel* : g₁ smbasel == g₂ smbasel)
    (smbaser* : g₁ smbaser == g₂ smbaser)
    (smgluel* : (x : de⊙ X) →
      smin* x (pt Y) ◃ apd g₂ (smgluel x) ==
      apd g₁ (smgluel x) ▹ smbasel*)
    (smgluer* : (y : de⊙ Y) →
      smin* (pt X) y ◃ apd g₂ (smgluer y) ==
      apd g₁ (smgluer y) ▹ smbaser*)
    where

    f : g₁ ∼ g₂
    f =
      Smash-elim
        {P = λ xy → g₁ xy == g₂ xy}
        smin*
        smbasel*
        smbaser*
        (λ x → ↓-=-in (smgluel* x))
        (λ y → ↓-=-in (smgluer* y))

  Smash-PathOver-elim = SmashPathOverElim.f

  module _ {k l} {X' : Ptd k} {Y' : Ptd l} (f : X ⊙→ X') (g : Y ⊙→ Y') where

    private
      module M = SmashRec
        {C = X' ∧ Y'}
        (λ x y → smin (fst f x) (fst g y))
        (smin (pt X') (pt Y'))
        (smin (pt X') (pt Y'))
        (λ x → ap (λ y' → smin (fst f x) y') (snd g) ∙ ∧-norm-l (fst f x))
        (λ y → ap (λ x' → smin x' (fst g y)) (snd f) ∙ ∧-norm-r (fst g y))

    abstract
      ∧-fmap : X ∧ Y → X' ∧ Y'
      ∧-fmap = M.f

      ∧-fmap-smin-β : ∀ x y → ∧-fmap (smin x y) ↦ smin (fst f x) (fst g y)
      ∧-fmap-smin-β = M.smin-β
      {-# REWRITE ∧-fmap-smin-β #-}

      ∧-fmap-smbasel-β : ∧-fmap smbasel ↦ smin (pt X') (pt Y')
      ∧-fmap-smbasel-β = M.smbasel-β
      {-# REWRITE ∧-fmap-smbasel-β #-}

      ∧-fmap-smbaser-β : ∧-fmap smbaser ↦ smin (pt X') (pt Y')
      ∧-fmap-smbaser-β = M.smbaser-β
      {-# REWRITE ∧-fmap-smbaser-β #-}

      ∧-fmap-smgluel-β' : ∀ x →
        ap ∧-fmap (smgluel x)
        ==
        ap (λ y' → smin (fst f x) y') (snd g) ∙
        ∧-norm-l (fst f x)
      ∧-fmap-smgluel-β' x = M.smgluel-β x

      ∧-fmap-smgluer-β' : ∀ y →
        ap ∧-fmap (smgluer y)
        ==
        ap (λ x' → smin x' (fst g y)) (snd f) ∙
        ∧-norm-r (fst g y)
      ∧-fmap-smgluer-β' = M.smgluer-β

    ∧-fmap-smgluel-β : ∀ x →
      ap ∧-fmap (smgluel x) ◃∎
      =ₛ
      ap (λ y' → smin (fst f x) y') (snd g) ◃∙
      ∧-norm-l (fst f x) ◃∎
    ∧-fmap-smgluel-β x = =ₛ-in (∧-fmap-smgluel-β' x)

    ∧-fmap-smgluer-β : ∀ y →
      ap ∧-fmap (smgluer y) ◃∎
      =ₛ
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      ∧-norm-r (fst g y) ◃∎
    ∧-fmap-smgluer-β y = =ₛ-in (∧-fmap-smgluer-β' y)

    ⊙∧-fmap : X ⊙∧ Y ⊙→ X' ⊙∧ Y'
    ⊙∧-fmap = ∧-fmap , ap2 smin (snd f) (snd g)

    ∧-fmap-norm-l : ∀ x →
      ap ∧-fmap (∧-norm-l x) ◃∎
      =ₛ
      ap (λ y' → smin (fst f x) y') (snd g) ◃∙
      smgluel (fst f x) ◃∙
      ! (smgluel (fst f (pt X))) ◃∙
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎
    ∧-fmap-norm-l x =
      ap ∧-fmap (∧-norm-l x) ◃∎
        =ₛ⟨ ap-seq-∙ ∧-fmap (∧-norm-l-seq x) ⟩
      ap ∧-fmap (smgluel x) ◃∙
      ap ∧-fmap (! (smgluel (pt X))) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! ∧-fmap (smgluel (pt X)) ⟩
      ap ∧-fmap (smgluel x) ◃∙
      ! (ap ∧-fmap (smgluel (pt X))) ◃∎
        =ₛ⟨ 0 & 1 & ∧-fmap-smgluel-β x ⟩
      ap (smin (fst f x)) (snd g) ◃∙
      ∧-norm-l (fst f x) ◃∙
      ! (ap ∧-fmap (smgluel (pt X))) ◃∎
        =ₛ⟨ 2 & 1 & !-=ₛ (∧-fmap-smgluel-β (pt X)) ⟩
      ap (smin (fst f x)) (snd g) ◃∙
      ∧-norm-l (fst f x) ◃∙
      ! (∧-norm-l (fst f (pt X))) ◃∙
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎
        =ₛ⟨ 2 & 1 & !-=ₛ (expand (∧-norm-l-seq (fst f (pt X)))) ⟩
      ap (smin (fst f x)) (snd g) ◃∙
      ∧-norm-l (fst f x) ◃∙
      ! (! (smgluel (pt X'))) ◃∙
      ! (smgluel (fst f (pt X))) ◃∙
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎
        =ₛ⟨ 1 & 1 & expand (∧-norm-l-seq (fst f x)) ⟩
      ap (smin (fst f x)) (snd g) ◃∙
      smgluel (fst f x) ◃∙
      ! (smgluel (pt X')) ◃∙
      ! (! (smgluel (pt X'))) ◃∙
      ! (smgluel (fst f (pt X))) ◃∙
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎
        =ₛ⟨ 2 & 2 & seq-!-inv-r (! (smgluel (pt X')) ◃∎) ⟩
      ap (smin (fst f x)) (snd g) ◃∙
      smgluel (fst f x) ◃∙
      ! (smgluel (fst f (pt X))) ◃∙
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎ ∎ₛ

    ∧-fmap-norm-r : ∀ y →
      ap ∧-fmap (∧-norm-r y) ◃∎
      =ₛ
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      smgluer (fst g y) ◃∙
      ! (smgluer (fst g (pt Y))) ◃∙
      ! (ap (λ x' → smin x' (fst g (pt Y))) (snd f)) ◃∎
    ∧-fmap-norm-r y =
      ap ∧-fmap (∧-norm-r y) ◃∎
        =ₛ⟨ ap-seq-∙ ∧-fmap (∧-norm-r-seq y) ⟩
      ap ∧-fmap (smgluer y) ◃∙
      ap ∧-fmap (! (smgluer (pt Y))) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! ∧-fmap (smgluer (pt Y)) ⟩
      ap ∧-fmap (smgluer y) ◃∙
      ! (ap ∧-fmap (smgluer (pt Y))) ◃∎
        =ₛ⟨ 0 & 1 & ∧-fmap-smgluer-β y ⟩
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      ∧-norm-r (fst g y) ◃∙
      ! (ap ∧-fmap (smgluer (pt Y))) ◃∎
        =ₛ⟨ 2 & 1 & !-=ₛ (∧-fmap-smgluer-β (pt Y)) ⟩
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      ∧-norm-r (fst g y) ◃∙
      ! (∧-norm-r (fst g (pt Y))) ◃∙
      ! (ap (λ x' → smin x' (fst g (pt Y))) (snd f)) ◃∎
        =ₛ⟨ 2 & 1 & !-=ₛ (expand (∧-norm-r-seq (fst g (pt Y)))) ⟩
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      ∧-norm-r (fst g y) ◃∙
      ! (! (smgluer (pt Y'))) ◃∙
      ! (smgluer (fst g (pt Y))) ◃∙
      ! (ap (λ x' → smin x' (fst g (pt Y))) (snd f)) ◃∎
        =ₛ⟨ 1 & 1 & expand (∧-norm-r-seq (fst g y)) ⟩
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      smgluer (fst g y) ◃∙
      ! (smgluer (pt Y')) ◃∙
      ! (! (smgluer (pt Y'))) ◃∙
      ! (smgluer (fst g (pt Y))) ◃∙
      ! (ap (λ x → smin x (fst g (pt Y))) (snd f)) ◃∎
        =ₛ⟨ 2 & 2 & seq-!-inv-r (! (smgluer (pt Y')) ◃∎) ⟩
      ap (λ x' → smin x' (fst g y)) (snd f) ◃∙
      smgluer (fst g y) ◃∙
      ! (smgluer (fst g (pt Y))) ◃∙
      ! (ap (λ x' → smin x' (fst g (pt Y))) (snd f)) ◃∎ ∎ₛ

module _ {i i' i'' j j' j''}
         {X : Ptd i} {X' : Ptd i'} {X'' : Ptd i''} (f : X ⊙→ X') (f' : X' ⊙→ X'')
         {Y : Ptd j} {Y' : Ptd j'} {Y'' : Ptd j''} (g : Y ⊙→ Y') (g' : Y' ⊙→ Y'') where

  ∧-fmap-comp : ∀ xy →
    ∧-fmap (f' ⊙∘ f) (g' ⊙∘ g) xy == ∧-fmap f' g' (∧-fmap f g xy)
  ∧-fmap-comp =
    Smash-elim {X = X} {Y = Y}
      {P = λ xy → ∧-fmap (f' ⊙∘ f) (g' ⊙∘ g) xy == ∧-fmap f' g' (∧-fmap f g xy)}
      (λ x y → idp)
      (! (ap2 smin (snd f') (snd g')))
      (! (ap2 smin (snd f') (snd g')))
      (λ x → ↓-='-in-=ₛ $
        idp ◃∙
        ap (∧-fmap f' g' ∘ ∧-fmap f g) (smgluel x) ◃∎
          =ₛ⟨ 0 & 1 & expand [] ⟩
        ap (∧-fmap f' g' ∘ ∧-fmap f g) (smgluel x) ◃∎
          =ₛ₁⟨ ap-∘ (∧-fmap f' g') (∧-fmap f g) (smgluel x) ⟩
        ap (∧-fmap f' g') (ap (∧-fmap f g) (smgluel x)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (∧-fmap f' g') (∧-fmap-smgluel-β f g x) ⟩
        ap (∧-fmap f' g') (ap (smin (fst f x)) (snd g)) ◃∙
        ap (∧-fmap f' g') (∧-norm-l (fst f x)) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-fmap f' g') (smin (fst f x)) (snd g) ⟩
        ap (smin (fst (f' ⊙∘ f) x) ∘ fst g') (snd g) ◃∙
        ap (∧-fmap f' g') (∧-norm-l (fst f x)) ◃∎
          =ₛ⟨ 1 & 1 & ∧-fmap-norm-l f' g' (fst f x) ⟩
        ap (smin (fst (f' ⊙∘ f) x) ∘ fst g') (snd g) ◃∙
        ap (smin (fst (f' ⊙∘ f) x)) (snd g') ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        ! (ap (smin (fst f' (pt X'))) (snd g')) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-∘ (smin (fst (f' ⊙∘ f) x)) (fst g') (snd g) ⟩
        ap (smin (fst (f' ⊙∘ f) x)) (ap (fst g') (snd g)) ◃∙
        ap (smin (fst (f' ⊙∘ f) x)) (snd g') ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        ! (ap (smin (fst f' (pt X'))) (snd g')) ◃∎
          =ₛ⟨ 0 & 2 & ∙-ap-seq (smin (fst (f' ⊙∘ f) x)) (ap (fst g') (snd g) ◃∙ snd g' ◃∎) ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        ! (ap (smin (fst f' (pt X'))) (snd g')) ◃∎
          =ₛ⟨ 3 & 0 & !ₛ (seq-!-inv-r (ap (λ x'' → smin x'' (pt Y'')) (snd f') ◃∎)) ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        ap (λ x'' → smin x'' (pt Y'')) (snd f') ◃∙
        ! (ap (λ x'' → smin x'' (pt Y'')) (snd f')) ◃∙
        ! (ap (smin (fst f' (pt X'))) (snd g')) ◃∎
          =ₛ⟨ 4 & 2 & !ₛ $ !-=ₛ $ ap2-out' smin (snd f') (snd g') ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        ap (λ x'' → smin x'' (pt Y'')) (snd f') ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 3 & 1 &
              =ₛ-in {t = smgluel (fst f' (pt X')) ◃∙ ! (smgluel (pt X'')) ◃∎} $
              homotopy-to-cst-ap (λ x'' → smin x'' (pt Y'')) smbasel smgluel (snd f') ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (fst f' (pt X'))) ◃∙
        smgluel (fst f' (pt X')) ◃∙
        ! (smgluel (pt X'')) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 2 & 2 & seq-!-inv-l (smgluel (fst f' (pt X')) ◃∎) ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        smgluel (fst (f' ⊙∘ f) x) ◃∙
        ! (smgluel (pt X'')) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 1 & 2 & contract ⟩
        ap (smin (fst f' (fst f x))) (snd (g' ⊙∘ g)) ◃∙
        ∧-norm-l (fst (f' ⊙∘ f) x) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (∧-fmap-smgluel-β (f' ⊙∘ f) (g' ⊙∘ g) x) ⟩
        ap (∧-fmap (f' ⊙∘ f) (g' ⊙∘ g)) (smgluel x) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎ ∎ₛ)
      (λ y → ↓-='-in-=ₛ $
        idp ◃∙
        ap (∧-fmap f' g' ∘ ∧-fmap f g) (smgluer y) ◃∎
          =ₛ⟨ 0 & 1 & expand [] ⟩
        ap (∧-fmap f' g' ∘ ∧-fmap f g) (smgluer y) ◃∎
          =ₛ₁⟨ ap-∘ (∧-fmap f' g') (∧-fmap f g) (smgluer y) ⟩
        ap (∧-fmap f' g') (ap (∧-fmap f g) (smgluer y)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (∧-fmap f' g') (∧-fmap-smgluer-β f g y) ⟩
        ap (∧-fmap f' g') (ap (λ x' → smin x' (fst g y)) (snd f)) ◃∙
        ap (∧-fmap f' g') (∧-norm-r (fst g y)) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-fmap f' g') (λ x' → smin x' (fst g y)) (snd f) ⟩
        ap (λ x' → smin (fst f' x') (fst (g' ⊙∘ g) y)) (snd f) ◃∙
        ap (∧-fmap f' g') (∧-norm-r (fst g y)) ◃∎
          =ₛ⟨ 1 & 1 & ∧-fmap-norm-r f' g' (fst g y) ⟩
        ap (λ x' → smin (fst f' x') (fst (g' ⊙∘ g) y)) (snd f) ◃∙
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd f') ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        ! (ap (λ x' → smin x' (fst g' (pt Y'))) (snd f')) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-∘ (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (fst f') (snd f) ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (ap (fst f') (snd f)) ◃∙
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd f') ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        ! (ap (λ x' → smin x' (fst g' (pt Y'))) (snd f')) ◃∎
          =ₛ⟨ 0 & 2 & ∙-ap-seq (λ x'' → smin x'' (fst (g' ⊙∘ g) y))
                               (ap (fst f') (snd f) ◃∙ snd f' ◃∎) ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        ! (ap (λ x' → smin x' (fst g' (pt Y'))) (snd f')) ◃∎
          =ₛ⟨ 3 & 0 & !ₛ (seq-!-inv-r (ap (smin (pt X'')) (snd g') ◃∎)) ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        ap (smin (pt X'')) (snd g') ◃∙
        ! (ap (smin (pt X'')) (snd g')) ◃∙
        ! (ap (λ x' → smin x' (fst g' (pt Y'))) (snd f')) ◃∎
          =ₛ⟨ 4 & 2 & !ₛ $ !-=ₛ $ ap2-out smin (snd f') (snd g') ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        ap (smin (pt X'')) (snd g') ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 3 & 1 &
              =ₛ-in {t = smgluer (fst g' (pt Y')) ◃∙ ! (smgluer (pt Y'')) ◃∎} $
              homotopy-to-cst-ap (smin (pt X'')) smbaser smgluer (snd g') ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (fst g' (pt Y'))) ◃∙
        smgluer (fst g' (pt Y')) ◃∙
        ! (smgluer (pt Y'')) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 2 & 2 & seq-!-inv-l (smgluer (fst g' (pt Y')) ◃∎) ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        smgluer (fst (g' ⊙∘ g) y) ◃∙
        ! (smgluer (pt Y'')) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 1 & 2 & contract ⟩
        ap (λ x'' → smin x'' (fst (g' ⊙∘ g) y)) (snd (f' ⊙∘ f)) ◃∙
        ∧-norm-r (fst (g' ⊙∘ g) y) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎
          =ₛ⟨ 0 & 2 & !ₛ (∧-fmap-smgluer-β (f' ⊙∘ f) (g' ⊙∘ g) y) ⟩
        ap (∧-fmap (f' ⊙∘ f) (g' ⊙∘ g)) (smgluer y) ◃∙
        ! (ap2 smin (snd f') (snd g')) ◃∎ ∎ₛ)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  module WedgeSwap =
    SmashRec {X = X} {Y = Y}
      {C = Y ∧ X}
      (λ x y → smin y x)
      (smin (pt Y) (pt X))
      (smin (pt Y) (pt X))
      ∧-norm-r
      ∧-norm-l

  ∧-swap : X ∧ Y → Y ∧ X
  ∧-swap = WedgeSwap.f

  ⊙∧-swap : X ⊙∧ Y ⊙→ Y ⊙∧ X
  ⊙∧-swap = ∧-swap , idp

  ∧-swap-norm-l-β : ∀ x →
    ap ∧-swap (∧-norm-l x) == ∧-norm-r x
  ∧-swap-norm-l-β x =
    ap ∧-swap (∧-norm-l x)
      =⟨ ap-∙ ∧-swap (smgluel x) (! (smgluel (pt X))) ⟩
    ap ∧-swap (smgluel x) ∙ ap ∧-swap (! (smgluel (pt X)))
      =⟨ ap2 _∙_
             (WedgeSwap.smgluel-β x)
             (ap-! ∧-swap (smgluel (pt X)) ∙
              ap ! (WedgeSwap.smgluel-β (pt X))) ⟩
    ∧-norm-r x ∙ ! (∧-norm-r (pt X))
      =⟨ ap (λ u → ∧-norm-r x ∙ ! u) (!-inv-r (smgluer (pt X))) ⟩
    ∧-norm-r x ∙ idp
      =⟨ ∙-unit-r (∧-norm-r x) ⟩
    ∧-norm-r x =∎

  ∧-swap-norm-r-β : ∀ y →
    ap ∧-swap (∧-norm-r y) == ∧-norm-l y
  ∧-swap-norm-r-β y =
    ap ∧-swap (∧-norm-r y)
      =⟨ ap-∙ ∧-swap (smgluer y) (! (smgluer (pt Y))) ⟩
    ap ∧-swap (smgluer y) ∙ ap ∧-swap (! (smgluer (pt Y)))
      =⟨ ap2 _∙_
             (WedgeSwap.smgluer-β y)
             (ap-! ∧-swap (smgluer (pt Y)) ∙
              ap ! (WedgeSwap.smgluer-β (pt Y))) ⟩
    ∧-norm-l y ∙ ! (∧-norm-l (pt Y))
      =⟨ ap (λ u → ∧-norm-l y ∙ ! u) (!-inv-r (smgluel (pt Y))) ⟩
    ∧-norm-l y ∙ idp
      =⟨ ∙-unit-r (∧-norm-l y) ⟩
    ∧-norm-l y =∎

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  module WedgeSwapInvolutive =
    SmashElim {X = X} {Y = Y}
      {P = λ xy → ∧-swap Y X (∧-swap X Y xy) == xy}
      (λ x y → idp)
      (smgluel (pt X))
      (smgluer (pt Y))
      (λ x → ↓-app=idf-in $ ! $
        ap (∧-swap Y X ∘ ∧-swap X Y) (smgluel x) ∙ smgluel (pt X)
          =⟨ ap (_∙ smgluel (pt X)) $
             ap-∘ (∧-swap Y X) (∧-swap X Y) (smgluel x) ⟩
        ap (∧-swap Y X) (ap (∧-swap X Y) (smgluel x)) ∙ smgluel (pt X)
          =⟨ ap (λ p → ap (∧-swap Y X) p ∙ smgluel (pt X)) $
             WedgeSwap.smgluel-β X Y x ⟩
        ap (∧-swap Y X) (∧-norm-r x) ∙ smgluel (pt X)
          =⟨ ap (_∙ smgluel (pt X)) (∧-swap-norm-r-β Y X x) ⟩
        ∧-norm-l x ∙ smgluel (pt X)
          =⟨ ∙-assoc (smgluel x) (! (smgluel (pt X))) (smgluel (pt X))⟩
        smgluel x ∙ ! (smgluel (pt X)) ∙ smgluel (pt X)
          =⟨ ap (smgluel x ∙_) (!-inv-l (smgluel (pt X))) ⟩
        smgluel x ∙ idp
          =⟨ ∙-unit-r (smgluel x) ⟩
        smgluel x
          =⟨ ! (∙'-unit-l (smgluel x)) ⟩
        idp ∙' smgluel x =∎)
      (λ y → ↓-app=idf-in $ ! $
        ap (∧-swap Y X ∘ ∧-swap X Y) (smgluer y) ∙ smgluer (pt Y)
          =⟨ ap (_∙ smgluer (pt Y)) $
             ap-∘ (∧-swap Y X) (∧-swap X Y) (smgluer y) ⟩
        ap (∧-swap Y X) (ap (∧-swap X Y) (smgluer y)) ∙ smgluer (pt Y)
          =⟨ ap (λ p → ap (∧-swap Y X) p ∙ smgluer (pt Y)) $
             WedgeSwap.smgluer-β X Y y ⟩
        ap (∧-swap Y X) (∧-norm-l y) ∙ smgluer (pt Y)
          =⟨ ap (_∙ smgluer (pt Y)) (∧-swap-norm-l-β Y X y) ⟩
        ∧-norm-r y ∙ smgluer (pt Y)
          =⟨ ∙-assoc (smgluer y) (! (smgluer (pt Y))) (smgluer (pt Y)) ⟩
        smgluer y ∙ ! (smgluer (pt Y)) ∙ smgluer (pt Y)
          =⟨ ap (smgluer y ∙_) (!-inv-l (smgluer (pt Y))) ⟩
        smgluer y ∙ idp
          =⟨ ∙-unit-r (smgluer y) ⟩
        smgluer y
          =⟨ ! (∙'-unit-l (smgluer y)) ⟩
        idp ∙' smgluer y =∎)

  ∧-swap-inv : ∀ xy → ∧-swap Y X (∧-swap X Y xy) == xy
  ∧-swap-inv = WedgeSwapInvolutive.f

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ∧-swap-is-equiv : is-equiv (∧-swap X Y)
  ∧-swap-is-equiv = is-eq _ (∧-swap Y X) (∧-swap-inv Y X) (∧-swap-inv X Y)

  ∧-swap-equiv : (X ∧ Y) ≃ (Y ∧ X)
  ∧-swap-equiv = ∧-swap X Y , ∧-swap-is-equiv

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
         (f : X ⊙→ X') (g : Y ⊙→ Y') where

  ∧-swap-naturality : ∀ xy →
    ∧-fmap g f (∧-swap X Y xy) == ∧-swap X' Y' (∧-fmap f g xy)
  ∧-swap-naturality =
    Smash-elim {X = X} {Y = Y}
      {P = λ xy → ∧-fmap g f (∧-swap X Y xy) == ∧-swap X' Y' (∧-fmap f g xy)}
      (λ x y → idp)
      (ap2 smin (snd g) (snd f))
      (ap2 smin (snd g) (snd f))
      (λ x → ↓-='-in-=ₛ $
        idp ◃∙
        ap (∧-swap X' Y' ∘ ∧-fmap f g) (smgluel x) ◃∎
          =ₛ⟨ 0 & 1 & expand [] ⟩
        ap (∧-swap X' Y' ∘ ∧-fmap f g) (smgluel x) ◃∎
          =ₛ₁⟨ ap-∘ (∧-swap X' Y') (∧-fmap f g) (smgluel x) ⟩
        ap (∧-swap X' Y') (ap (∧-fmap f g) (smgluel x)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (∧-swap X' Y') (∧-fmap-smgluel-β f g x) ⟩
        ap (∧-swap X' Y') (ap (smin (fst f x)) (snd g)) ◃∙
        ap (∧-swap X' Y') (∧-norm-l (fst f x)) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-swap X' Y') (smin (fst f x)) (snd g) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        ap (∧-swap X' Y') (∧-norm-l (fst f x)) ◃∎
          =ₛ₁⟨ 1 & 1 & ∧-swap-norm-l-β X' Y' (fst f x) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        ∧-norm-r (fst f x) ◃∎
          =ₛ⟨ 1 & 1 & expand (∧-norm-r-seq (fst f x)) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        smgluer (fst f x) ◃∙
        ! (smgluer (pt X')) ◃∎
          =ₛ⟨ 2 & 0 & !ₛ (seq-!-inv-l (smgluer (fst f (pt X)) ◃∎)) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        smgluer (fst f x) ◃∙
        ! (smgluer (fst f (pt X))) ◃∙
        smgluer (fst f (pt X)) ◃∙
        ! (smgluer (pt X')) ◃∎
          =ₛ₁⟨ 3 & 2 & ! (homotopy-to-cst-ap (smin (pt Y')) smbaser smgluer (snd f)) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        smgluer (fst f x) ◃∙
        ! (smgluer (fst f (pt X))) ◃∙
        ap (smin (pt Y')) (snd f) ◃∎
          =ₛ⟨ 3 & 0 & !ₛ (seq-!-inv-l (ap (λ y' → smin y' (fst f (pt X))) (snd g) ◃∎)) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        smgluer (fst f x) ◃∙
        ! (smgluer (fst f (pt X))) ◃∙
        ! (ap (λ y' → smin y' (fst f (pt X))) (snd g)) ◃∙
        ap (λ y' → smin y' (fst f (pt X))) (snd g) ◃∙
        ap (smin (pt Y')) (snd f) ◃∎
          =ₛ⟨ 4 & 2 & !ₛ (ap2-out smin (snd g) (snd f)) ⟩
        ap (λ y' → smin y' (fst f x)) (snd g) ◃∙
        smgluer (fst f x) ◃∙
        ! (smgluer (fst f (pt X))) ◃∙
        ! (ap (λ y' → smin y' (fst f (pt X))) (snd g)) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ⟨ 0 & 4 & !ₛ (∧-fmap-norm-r g f x) ⟩
        ap (∧-fmap g f) (∧-norm-r x) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ₁⟨ 0 & 1 & ! (ap (ap (∧-fmap g f)) (WedgeSwap.smgluel-β X Y x)) ⟩
        ap (∧-fmap g f) (ap (∧-swap X Y) (smgluel x)) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-fmap g f) (∧-swap X Y) (smgluel x) ⟩
        ap (∧-fmap g f ∘ ∧-swap X Y) (smgluel x) ◃∙
        ap2 smin (snd g) (snd f) ◃∎ ∎ₛ)
      (λ y → ↓-='-in-=ₛ $
        idp ◃∙
        ap (∧-swap X' Y' ∘ ∧-fmap f g) (smgluer y) ◃∎
          =ₛ⟨ 0 & 1 & expand [] ⟩
        ap (∧-swap X' Y' ∘ ∧-fmap f g) (smgluer y) ◃∎
          =ₛ₁⟨ ap-∘ (∧-swap X' Y') (∧-fmap f g) (smgluer y) ⟩
        ap (∧-swap X' Y') (ap (∧-fmap f g) (smgluer y)) ◃∎
          =ₛ⟨ ap-seq-=ₛ (∧-swap X' Y') (∧-fmap-smgluer-β f g y) ⟩
        ap (∧-swap X' Y') (ap (λ x' → smin x' (fst g y)) (snd f)) ◃∙
        ap (∧-swap X' Y') (∧-norm-r (fst g y)) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-swap X' Y') (λ x' → smin x' (fst g y)) (snd f) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        ap (∧-swap X' Y') (∧-norm-r (fst g y)) ◃∎
          =ₛ₁⟨ 1 & 1 & ∧-swap-norm-r-β X' Y' (fst g y) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        ∧-norm-l (fst g y) ◃∎
          =ₛ⟨ 1 & 1 & expand (∧-norm-l-seq (fst g y)) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        smgluel (fst g y) ◃∙
        ! (smgluel (pt Y')) ◃∎
          =ₛ⟨ 2 & 0 & !ₛ (seq-!-inv-l (smgluel (fst g (pt Y)) ◃∎)) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        smgluel (fst g y) ◃∙
        ! (smgluel (fst g (pt Y))) ◃∙
        smgluel (fst g (pt Y)) ◃∙
        ! (smgluel (pt Y')) ◃∎
          =ₛ₁⟨ 3 & 2 & ! (homotopy-to-cst-ap (λ y' → smin y' (pt X')) smbasel smgluel (snd g)) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        smgluel (fst g y) ◃∙
        ! (smgluel (fst g (pt Y))) ◃∙
        ap (λ y' → smin y' (pt X')) (snd g) ◃∎
          =ₛ⟨ 3 & 0 & !ₛ (seq-!-inv-l (ap (smin (fst g (pt Y))) (snd f) ◃∎)) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        smgluel (fst g y) ◃∙
        ! (smgluel (fst g (pt Y))) ◃∙
        ! (ap (smin (fst g (pt Y))) (snd f)) ◃∙
        ap (smin (fst g (pt Y))) (snd f) ◃∙
        ap (λ y' → smin y' (pt X')) (snd g) ◃∎
          =ₛ⟨ 4 & 2 & !ₛ (ap2-out' smin (snd g) (snd f)) ⟩
        ap (smin (fst g y)) (snd f) ◃∙
        smgluel (fst g y) ◃∙
        ! (smgluel (fst g (pt Y))) ◃∙
        ! (ap (smin (fst g (pt Y))) (snd f)) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ⟨ 0 & 4 & !ₛ (∧-fmap-norm-l g f y) ⟩
        ap (∧-fmap g f) (∧-norm-l y) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ₁⟨ 0 & 1 & ! (ap (ap (∧-fmap g f)) (WedgeSwap.smgluer-β X Y y)) ⟩
        ap (∧-fmap g f) (ap (∧-swap X Y) (smgluer y)) ◃∙
        ap2 smin (snd g) (snd f) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap (∧-fmap g f) (∧-swap X Y) (smgluer y) ⟩
        ap (∧-fmap g f ∘ ∧-swap X Y) (smgluer y) ◃∙
        ap2 smin (snd g) (snd f) ◃∎ ∎ₛ)

  ∧-swap-fmap : ∀ xy →
    ∧-swap Y' X' (∧-fmap g f (∧-swap X Y xy)) == ∧-fmap f g xy
  ∧-swap-fmap xy =
    ∧-swap Y' X' (∧-fmap g f (∧-swap X Y xy))
      =⟨ ap (∧-swap Y' X') (∧-swap-naturality xy) ⟩
    ∧-swap Y' X' (∧-swap X' Y' (∧-fmap f g xy))
      =⟨ ∧-swap-inv X' Y' (∧-fmap f g xy) ⟩
    ∧-fmap f g xy =∎
