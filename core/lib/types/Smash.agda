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

    {-∧-fmap-norm-l : ∀ x →
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
      ! (ap (smin (fst f (pt X))) (snd g)) ◃∎ ∎ₛ-}
