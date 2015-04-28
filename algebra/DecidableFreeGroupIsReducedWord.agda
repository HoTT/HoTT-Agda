{-# OPTIONS --without-K #-}

open import HoTT hiding (_::_)

module algebra.DecidableFreeGroupIsReducedWord {i} (A : Type i) (dec : has-dec-eq A) where

  open import algebra.Word A
  open import algebra.ReducedWord A dec

  -- Some helper functions.

  tail-is-reduced : (x : A) (w : Word) → is-reduced (x :: w) → is-reduced w
  tail-is-reduced x nil         red = lift unit
  tail-is-reduced x (y    :: w) red = red
  tail-is-reduced x (y inv:: w) red = snd red

  tail'-is-reduced : (x : A) (w : Word) → is-reduced (x inv:: w) → is-reduced w
  tail'-is-reduced x nil         red = lift unit
  tail'-is-reduced x (y    :: w) red = snd red
  tail'-is-reduced x (y inv:: w) red = red

  -- Conversion function.

  ReducedWord⇒FreeGroup : ReducedWord → FreeGroup A
  ReducedWord⇒FreeGroup (w , red) = f w red
    where
      f : (w : Word) → is-reduced w → FreeGroup A
      f nil         _ = fg-nil
      f (x    :: w) r = x     fg:: f w (tail-is-reduced  x w r)
      f (x inv:: w) r = x fg-inv:: f w (tail'-is-reduced x w r)

  infixr 60 _rw::_ _rw-inv::_

  _rw::_ : A → ReducedWord → ReducedWord
  x rw:: (nil , red) = ((x :: nil) , lift unit)
  x rw:: ((y    :: w) , red) = ((x :: y :: w) , red)
  x rw:: ((y inv:: w) , red) with dec x y
  x rw:: ((y inv:: w) , red) | inl x=y = (w , tail'-is-reduced y w red)
  x rw:: ((y inv:: w) , red) | inr x≠y = ((x :: y inv:: w) , (x≠y , red))

  _rw-inv::_ : A → ReducedWord → ReducedWord
  x rw-inv:: (nil , red) = ((x inv:: nil) , lift unit)
  x rw-inv:: ((y inv:: w) , red) = ((x inv:: y inv:: w) , red)
  x rw-inv:: ((y    :: w) , red) with dec x y
  x rw-inv:: ((y    :: w) , red) | inl eq  = (w , tail-is-reduced y w red)
  x rw-inv:: ((y    :: w) , red) | inr neq = ((x inv:: y :: w) , (neq , red))

  abstract
    rw-inv-r : ∀ x w → x rw:: x rw-inv:: w == w
    rw-inv-r x (nil , red) with dec x x
    rw-inv-r x (nil , red) | inl x=x = idp
    rw-inv-r x (nil , red) | inr x≠x = ⊥-rec (x≠x idp)
    rw-inv-r x ((y :: w)         , red) with dec x y
    rw-inv-r x ((y :: nil)       , red) | inl x=y = x=y |in-ctx _
    rw-inv-r x ((y :: z    :: w) , red) | inl x=y = x=y |in-ctx _
    rw-inv-r x ((y :: z inv:: w) , red) | inl x=y with dec x z
    rw-inv-r x ((y :: z inv:: w) , red) | inl x=y | inl x=z = ⊥-rec (fst red (! x=y ∙ x=z))
    rw-inv-r x ((y :: z inv:: w) , red) | inl x=y | inr x≠z = ReducedWord=-in (x=y |in-ctx _)
    rw-inv-r x ((y :: w)         , red) | inr x≠y with dec x x
    rw-inv-r x ((y :: w)         , red) | inr x≠y | inl x=x = idp
    rw-inv-r x ((y :: w)         , red) | inr x≠y | inr x≠x = ⊥-rec (x≠x idp)
    rw-inv-r x ((y inv:: w)      , red) with dec x x
    rw-inv-r x ((y inv:: w)      , red) | inl x=x = idp
    rw-inv-r x ((y inv:: w)      , red) | inr x≠x = ⊥-rec (x≠x idp)

  abstract
    rw-inv-l : ∀ x w → x rw-inv:: x rw:: w == w
    rw-inv-l x (nil , red) with dec x x
    rw-inv-l x (nil , red) | inl x=x = idp
    rw-inv-l x (nil , red) | inr x≠x = ⊥-rec (x≠x idp)
    rw-inv-l x ((y inv:: w)         , red) with dec x y
    rw-inv-l x ((y inv:: nil)       , red) | inl x=y = x=y |in-ctx _
    rw-inv-l x ((y inv:: z inv:: w) , red) | inl x=y = x=y |in-ctx _
    rw-inv-l x ((y inv:: z    :: w) , red) | inl x=y with dec x z
    rw-inv-l x ((y inv:: z    :: w) , red) | inl x=y | inl x=z = ⊥-rec (fst red (! x=y ∙ x=z))
    rw-inv-l x ((y inv:: z    :: w) , red) | inl x=y | inr x≠z = ReducedWord=-in (x=y |in-ctx _)
    rw-inv-l x ((y inv:: w)         , red) | inr x≠y with dec x x
    rw-inv-l x ((y inv:: w)         , red) | inr x≠y | inl x=x = idp
    rw-inv-l x ((y inv:: w)         , red) | inr x≠y | inr x≠x = ⊥-rec (x≠x idp)
    rw-inv-l x ((y    :: w)         , red) with dec x x
    rw-inv-l x ((y    :: w)         , red) | inl x=x = idp
    rw-inv-l x ((y    :: w)         , red) | inr x≠x = ⊥-rec (x≠x idp)

  FreeGroup⇒ReducedWord : FreeGroup A → ReducedWord
  FreeGroup⇒ReducedWord = FreeGroup-rec ReducedWord-is-set
    (nil , lift unit)
    (λ x  _  rw → x     rw:: rw)
    (λ x  _  rw → x rw-inv:: rw)
    (λ x {_} rw → rw-inv-l x rw)
    (λ x {_} rw → rw-inv-r x rw)

  abstract
    rw::-reduced : ∀ x w (red : is-reduced (x :: w))
      → x rw:: (w , tail-is-reduced x w red) == ((x :: w) , red)
    rw::-reduced x nil         red = idp
    rw::-reduced x (y    :: w) red = idp
    rw::-reduced x (y inv:: w) red with dec x y
    rw::-reduced x (y inv:: w) red | inl x=y = ⊥-rec (fst red x=y)
    rw::-reduced x (y inv:: w) red | inr x≠y = ReducedWord=-in idp

  abstract
    rw-inv::-reduced : ∀ x w (red : is-reduced (x inv:: w))
      → x rw-inv:: (w , tail'-is-reduced x w red) == ((x inv:: w) , red)
    rw-inv::-reduced x nil         red = idp
    rw-inv::-reduced x (y inv:: w) red = idp
    rw-inv::-reduced x (y    :: w) red with dec x y
    rw-inv::-reduced x (y    :: w) red | inl x=y = ⊥-rec (fst red x=y)
    rw-inv::-reduced x (y    :: w) red | inr x≠y = ReducedWord=-in idp

  ReducedWord⇒FreeGroup⇒ReducedWord :
    ∀ w → FreeGroup⇒ReducedWord (ReducedWord⇒FreeGroup w) == w 
  ReducedWord⇒FreeGroup⇒ReducedWord (w , red) = f w red
    where
      f : ∀ w red → FreeGroup⇒ReducedWord (ReducedWord⇒FreeGroup (w , red)) == w , red
      f nil _ = idp
      f (x :: w) red =
        x rw:: FreeGroup⇒ReducedWord (ReducedWord⇒FreeGroup (w , tail-is-reduced x w red))
          =⟨ f w (tail-is-reduced x w red) |in-ctx (λ w → x rw:: w) ⟩
        x rw:: (w , tail-is-reduced x w red)
          =⟨ rw::-reduced x w red ⟩
        (x :: w) , red
          ∎
      f (x inv:: w) red =
        x rw-inv:: FreeGroup⇒ReducedWord (ReducedWord⇒FreeGroup (w , tail'-is-reduced x w red))
          =⟨ f w (tail'-is-reduced x w red) |in-ctx (λ w → x rw-inv:: w) ⟩
        x rw-inv:: (w , tail'-is-reduced x w red)
          =⟨ rw-inv::-reduced x w red ⟩
        (x inv:: w) , red
          ∎

  ReducedWord⇒FreeGroup-rw:: : ∀ x w
    → ReducedWord⇒FreeGroup (x rw:: w) == x fg:: ReducedWord⇒FreeGroup w
  ReducedWord⇒FreeGroup-rw:: x (nil , red) = idp
  ReducedWord⇒FreeGroup-rw:: x ((y     :: w) , red) = idp
  ReducedWord⇒FreeGroup-rw:: x ((y  inv:: w) , red) with dec x y
  ReducedWord⇒FreeGroup-rw:: x ((.x inv:: w) , red) | inl idp =
    ! (fg-inv-r x (ReducedWord⇒FreeGroup (w , tail'-is-reduced x w red)))
  ReducedWord⇒FreeGroup-rw:: x ((y  inv:: w) , red) | inr x≠y = idp

  ReducedWord⇒FreeGroup-rw-inv:: : ∀ x w
    → ReducedWord⇒FreeGroup (x rw-inv:: w) == x fg-inv:: ReducedWord⇒FreeGroup w
  ReducedWord⇒FreeGroup-rw-inv:: x (nil , red) = idp
  ReducedWord⇒FreeGroup-rw-inv:: x ((y  inv:: w) , red) = idp
  ReducedWord⇒FreeGroup-rw-inv:: x ((y     :: w) , red) with dec x y
  ReducedWord⇒FreeGroup-rw-inv:: x ((.x    :: w) , red) | inl idp =
    ! (fg-inv-l x (ReducedWord⇒FreeGroup (w , tail-is-reduced x w red)))
  ReducedWord⇒FreeGroup-rw-inv:: x ((y     :: w) , red) | inr x≠y = idp

  FreeGroup⇒ReducedWord⇒FreeGroup : ∀ fg
    → ReducedWord⇒FreeGroup (FreeGroup⇒ReducedWord fg) == fg
  FreeGroup⇒ReducedWord⇒FreeGroup = FreeGroup-elim
    (λ _ → =-preserves-set FreeGroup-is-set)
    idp
    (λ x {fg} fg* → 
      ReducedWord⇒FreeGroup (x rw:: FreeGroup⇒ReducedWord fg)
        =⟨ ReducedWord⇒FreeGroup-rw:: x (FreeGroup⇒ReducedWord fg) ⟩
      x fg:: ReducedWord⇒FreeGroup (FreeGroup⇒ReducedWord fg)
        =⟨ fg* |in-ctx (_fg::_ x) ⟩
      x fg:: fg
        ∎)
    (λ x {fg} fg* → 
      ReducedWord⇒FreeGroup (x rw-inv:: FreeGroup⇒ReducedWord fg)
        =⟨ ReducedWord⇒FreeGroup-rw-inv:: x (FreeGroup⇒ReducedWord fg) ⟩
      x fg-inv:: ReducedWord⇒FreeGroup (FreeGroup⇒ReducedWord fg)
        =⟨ fg* |in-ctx (_fg-inv::_ x) ⟩
      x fg-inv:: fg
        ∎)
    (λ x {fg} fg* → prop-has-all-paths-↓ (FreeGroup-is-set _ _))
    (λ x {fg} fg* → prop-has-all-paths-↓ (FreeGroup-is-set _ _))

FreeGroup≃ReducedWord : FreeGroup A ≃ ReducedWord
FreeGroup≃ReducedWord = FreeGroup⇒ReducedWord ,
  is-eq
    _
    ReducedWord⇒FreeGroup
    ReducedWord⇒FreeGroup⇒ReducedWord
    FreeGroup⇒ReducedWord⇒FreeGroup
