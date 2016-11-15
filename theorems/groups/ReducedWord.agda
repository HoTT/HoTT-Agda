{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.ReducedWord {i} {A : Type i} (dec : has-dec-eq A) where

  is-reduced : Word A → Type i
  is-reduced nil                   = Lift ⊤
  is-reduced (_     :: nil)        = Lift ⊤
  is-reduced (inl x :: inl y :: w) = is-reduced (inl y :: w)
  is-reduced (inl x :: inr y :: w) = (x ≠ y) × is-reduced (inr y :: w)
  is-reduced (inr x :: inl y :: w) = (x ≠ y) × is-reduced (inl y :: w)
  is-reduced (inr x :: inr y :: w) = is-reduced (inr y :: w)

  -- Everything is a set.

  A-is-set : is-set A
  A-is-set = dec-eq-is-set dec

  PlusMinus-has-dec-eq : has-dec-eq (PlusMinus A)
  PlusMinus-has-dec-eq (inl x) (inl y) with dec x y
  PlusMinus-has-dec-eq (inl x) (inl y) | inl p  = inl $ ap inl p
  PlusMinus-has-dec-eq (inl x) (inl y) | inr ¬p = inr $ ¬p ∘ lower ∘ Coprod=-in
  PlusMinus-has-dec-eq (inl x) (inr y) = inr $ lower ∘ Coprod=-in
  PlusMinus-has-dec-eq (inr x) (inl y) = inr $ lower ∘ Coprod=-in
  PlusMinus-has-dec-eq (inr x) (inr y) with dec x y
  PlusMinus-has-dec-eq (inr x) (inr y) | inl p  = inl $ ap inr p
  PlusMinus-has-dec-eq (inr x) (inr y) | inr ¬p = inr $ ¬p ∘ lower ∘ Coprod=-in

  Word-has-dec-eq : has-dec-eq (Word A)
  Word-has-dec-eq nil nil = inl idp
  Word-has-dec-eq nil (_ :: w) = inr $ lower ∘ List=-in
  Word-has-dec-eq (_ :: v) nil = inr $ lower ∘ List=-in
  Word-has-dec-eq (x :: v) (y :: w) with PlusMinus-has-dec-eq x y
  Word-has-dec-eq (x :: v) (y :: w) | inl x=y with Word-has-dec-eq v w
  Word-has-dec-eq (x :: v) (y :: w) | inl x=y | inl v=w = inl $ List=-out (x=y , v=w)
  Word-has-dec-eq (x :: v) (y :: w) | inl x=y | inr v≠w = inr $ v≠w ∘ snd ∘ List=-in
  Word-has-dec-eq (x :: v) (y :: w) | inr x≠y = inr $ x≠y ∘ fst ∘ List=-in

  Word-is-set : is-set (Word A)
  Word-is-set = dec-eq-is-set Word-has-dec-eq

  is-reduced-is-prop : {w : Word A} → is-prop (is-reduced w)
  is-reduced-is-prop {nil}                 = Lift-level Unit-is-prop
  is-reduced-is-prop {x    :: nil}         = Lift-level Unit-is-prop
  is-reduced-is-prop {inl x :: inl y :: l} = is-reduced-is-prop {inl y :: l}
  is-reduced-is-prop {inl x :: inr y :: l} = ×-level (→-is-prop (λ x₁ → λ ())) (is-reduced-is-prop {inr y :: l})
  is-reduced-is-prop {inr x :: inl y :: l} = ×-level (→-is-prop (λ x₁ → λ ())) (is-reduced-is-prop {inl y :: l})
  is-reduced-is-prop {inr x :: inr y :: l} = is-reduced-is-prop {inr y :: l}

  is-reduced-prop : SubtypeProp (Word A) i
  is-reduced-prop = is-reduced , λ w → is-reduced-is-prop {w}

  -- The subtype

  ReducedWord : Type i
  ReducedWord = Subtype is-reduced-prop

  ReducedWord-is-set : is-set ReducedWord
  ReducedWord-is-set = Subtype-level is-reduced-prop Word-is-set

  -- Identifications in [ReducedWord].

  ReducedWord= : ReducedWord → ReducedWord → Type i
  ReducedWord= = Subtype= is-reduced-prop

  ReducedWord=-out : {x y : ReducedWord} → ReducedWord= x y → x == y
  ReducedWord=-out = Subtype=-out is-reduced-prop

  -- The group structure of reduced words

  private
    rw-unit : ReducedWord
    rw-unit = nil , lift tt

    abstract
      tail-is-reduced : ∀ x w → is-reduced (x :: w) → is-reduced w
      tail-is-reduced x nil red = lift tt
      tail-is-reduced (inl x) (inl y :: w) red = red
      tail-is-reduced (inl x) (inr y :: w) red = snd red
      tail-is-reduced (inr x) (inl y :: w) red = snd red
      tail-is-reduced (inr x) (inr y :: w) red = red

    rw-cons : PlusMinus A → ReducedWord → ReducedWord
    rw-cons x (nil , _) = (x :: nil) , lift tt
    rw-cons (inl x) ((inl y :: l) , red) = (inl x :: inl y :: l) , red
    rw-cons (inl x) ((inr y :: l) , red) with dec x y
    rw-cons (inl x) ((inr y :: l) , red) | inl p = l , tail-is-reduced (inr y) l red
    rw-cons (inl x) ((inr y :: l) , red) | inr ¬p = (inl x :: inr y :: l) , (¬p , red)
    rw-cons (inr x) ((inl y :: l) , red) with dec x y
    rw-cons (inr x) ((inl y :: l) , red) | inl p = l , tail-is-reduced (inl y) l red
    rw-cons (inr x) ((inl y :: l) , red) | inr ¬p = (inr x :: inl y :: l) , (¬p , red)
    rw-cons (inr x) ((inr y :: l) , red) = (inr x :: inr y :: l) , red

    rw-++' : Word A → ReducedWord → ReducedWord
    rw-++' w₁ rw₂ = foldr rw-cons rw₂ w₁

    reduce : Word A → ReducedWord
    reduce w = rw-++' w rw-unit

    rw-++ : ReducedWord → ReducedWord → ReducedWord
    rw-++ rw₁ rw₂ = rw-++' (fst rw₁) rw₂

    abstract
      head2-is-reduced : ∀ x y w → is-reduced (x :: y :: w) → is-reduced (x :: y :: nil)
      head2-is-reduced (inl x) (inl y) w red = lift tt
      head2-is-reduced (inl x) (inr y) w red = fst red , lift tt
      head2-is-reduced (inr x) (inl y) w red = fst red , lift tt
      head2-is-reduced (inr x) (inr y) w red = lift tt

      rw-cons-reduced : ∀ x w
        → (red : is-reduced w)
        → (red' : is-reduced (x :: w))
        → rw-cons x (w , red) == (x :: w) , red'
      rw-cons-reduced x nil _ _ = ReducedWord=-out idp
      rw-cons-reduced (inl x) (inl y :: w) _ red' = ReducedWord=-out idp
      rw-cons-reduced (inl x) (inr y :: w) _ red' with dec x y
      rw-cons-reduced (inl x) (inr y :: w) _ red' | inl p = ⊥-rec $ fst red' $ p
      rw-cons-reduced (inl x) (inr y :: w) _ red' | inr ¬p = ReducedWord=-out idp
      rw-cons-reduced (inr x) (inl y :: w) _ red' with dec x y
      rw-cons-reduced (inr x) (inl y :: w) _ red' | inl p = ⊥-rec $ fst red' $ p
      rw-cons-reduced (inr x) (inl y :: w) _ red' | inr ¬p = ReducedWord=-out idp
      rw-cons-reduced (inr x) (inr y :: w) _ red' = ReducedWord=-out idp

      rw-++-unit-r' : ∀ w (red : is-reduced w) → rw-++ (w , red) rw-unit == (w , red)
      rw-++-unit-r' nil _ = ReducedWord=-out idp
      rw-++-unit-r' (x :: w) red =
          ap (rw-cons x) ( ReducedWord=-out idp
                         ∙ rw-++-unit-r' w (tail-is-reduced x w red))
        ∙ rw-cons-reduced x w (tail-is-reduced x w red) red

    -- assoc
    abstract
      rw-cons-flip : ∀ x w red red'
        → rw-cons x ((flip x :: w) , red) == w , red'
      rw-cons-flip (inl x) w _ _ with dec x x
      rw-cons-flip (inl x) w _ _ | inl x=x = ReducedWord=-out idp
      rw-cons-flip (inl x) w _ _ | inr x≠x = ⊥-rec (x≠x idp)
      rw-cons-flip (inr x) w _ _ with dec x x
      rw-cons-flip (inr x) w _ _ | inl x=x = ReducedWord=-out idp
      rw-cons-flip (inr x) w _ _ | inr x≠x = ⊥-rec (x≠x idp)

      rw-cons-cons-flip : ∀ x rw
        → rw-cons x (rw-cons (flip x) rw) == rw
      rw-cons-cons-flip x (nil , red) = rw-cons-flip x nil _ red
      rw-cons-cons-flip (inl x) ((inl y :: w) , red) with dec x y
      rw-cons-cons-flip (inl x) ((inl y :: w) , red) | inl x=y =
          rw-cons-reduced (inl x) w _ (transport! (λ z → is-reduced (inl z :: w)) x=y red)
        ∙ ReducedWord=-out (ap (λ z → inl z :: w) x=y)
      rw-cons-cons-flip (inl x) ((inl y :: w) , red) | inr x≠y =
        rw-cons-flip (inl x) (inl y :: w) (x≠y , red) red
      rw-cons-cons-flip (inl x) ((inr y :: w) , red) = rw-cons-flip (inl x) (inr y :: w) red red
      rw-cons-cons-flip (inr x) ((inl y :: w) , red) = rw-cons-flip (inr x) (inl y :: w) red red
      rw-cons-cons-flip (inr x) ((inr y :: w) , red) with dec x y
      rw-cons-cons-flip (inr x) ((inr y :: w) , red) | inl x=y =
          rw-cons-reduced (inr x) w _ (transport! (λ z → is-reduced (inr z :: w)) x=y red)
        ∙ ReducedWord=-out (ap (λ z → inr z :: w) x=y)
      rw-cons-cons-flip (inr x) ((inr y :: w) , red) | inr x≠y =
        rw-cons-flip (inr x) (inr y :: w) (x≠y , red) red

      rw-++-cons : ∀ x rw₁ rw₂
        →  rw-++ (rw-cons x rw₁) rw₂
        == rw-cons x (rw-++ rw₁ rw₂)
      rw-++-cons x       (nil           , _) rw₂ = idp
      rw-++-cons (inl x) ((inl y :: w₁) , _) rw₂ = idp
      rw-++-cons (inl x) ((inr y :: w₁) , _) rw₂ with dec x y
      rw-++-cons (inl x) ((inr y :: w₁) , _) rw₂ | inl p rewrite p =
        ! (rw-cons-cons-flip (inl y) (rw-++' w₁ rw₂))
      rw-++-cons (inl x) ((inr y :: w₁) , _) rw₂ | inr ¬p = idp
      rw-++-cons (inr x) ((inl y :: w₁) , _) rw₂ with dec x y
      rw-++-cons (inr x) ((inl y :: w₁) , _) rw₂ | inl p rewrite p =
        ! (rw-cons-cons-flip (inr y) (rw-++' w₁ rw₂))
      rw-++-cons (inr x) ((inl y :: w₁) , _) rw₂ | inr ¬p = idp
      rw-++-cons (inr x) ((inr y :: w₁) , _) rw₂ = idp

      rw-++-assoc' : ∀ w₁ rw₂ rw₃
        →  rw-++ (rw-++' w₁ rw₂) rw₃
        == rw-++' w₁ (rw-++' (fst rw₂) rw₃)
      rw-++-assoc' nil rw₂ rw = idp
      rw-++-assoc' (x :: w₁) rw₂ rw₃ =
          rw-++-cons x (rw-++' w₁ rw₂) rw₃
        ∙ ap (rw-cons x) (rw-++-assoc' w₁ rw₂ rw₃)

    -- inv
    abstract
      cons-is-reduced : ∀ x y w → is-reduced (x :: y :: nil) → is-reduced (y :: w)
        → is-reduced (x :: y :: w)
      cons-is-reduced (inl x) (inl y) _ _    red₂ = red₂
      cons-is-reduced (inl x) (inr y) _ red₁ red₂ = fst red₁ , red₂
      cons-is-reduced (inr x) (inl y) _ red₁ red₂ = fst red₁ , red₂
      cons-is-reduced (inr x) (inr y) _ _    red₂ = red₂

      ++-is-reduced : ∀ w₁ x w₂ → is-reduced (w₁ ++ (x :: nil)) → is-reduced (x :: w₂)
        → is-reduced ((w₁ ++ (x :: nil)) ++ w₂)
      ++-is-reduced nil            _ _  _    red₂ = red₂
      ++-is-reduced (x :: nil)     y w₂ red₁ red₂ = cons-is-reduced x y w₂ red₁ red₂
      ++-is-reduced (x :: y :: w₁) z w₂ red₁ red₂ =
        cons-is-reduced x y ((w₁ ++ (z :: nil)) ++ w₂)
          (head2-is-reduced x y (w₁ ++ (z :: nil)) red₁)
          (++-is-reduced (y :: w₁) z w₂ (tail-is-reduced x (y :: w₁ ++ (z :: nil)) red₁) red₂)

      swap2-is-reduced : ∀ x y → is-reduced (x :: y :: nil) → is-reduced (y :: x :: nil)
      swap2-is-reduced (inl x) (inl y) red = lift tt
      swap2-is-reduced (inl x) (inr y) red = fst red ∘ ! , lift tt
      swap2-is-reduced (inr x) (inl y) red = fst red ∘ ! , lift tt
      swap2-is-reduced (inr x) (inr y) red = lift tt

      reverse-is-reduced : ∀ w → is-reduced w → is-reduced (reverse w)
      reverse-is-reduced nil red = red
      reverse-is-reduced (x :: nil) red = red
      reverse-is-reduced (x :: y :: w) red =
        ++-is-reduced
          (reverse w) y (x :: nil)
          (reverse-is-reduced (y :: w) (tail-is-reduced x (y :: w) red))
          (swap2-is-reduced x y (head2-is-reduced x y w red))

      flip2-is-reduced : ∀ x y → is-reduced (x :: y :: nil) → is-reduced (flip x :: flip y :: nil)
      flip2-is-reduced (inl x) (inl y) red = red
      flip2-is-reduced (inl x) (inr y) red = red
      flip2-is-reduced (inr x) (inl y) red = red
      flip2-is-reduced (inr x) (inr y) red = red

      Word-flip-is-reduced : ∀ w → is-reduced w → is-reduced (Word-flip w)
      Word-flip-is-reduced nil           red = red
      Word-flip-is-reduced (x :: nil)    red = red
      Word-flip-is-reduced (x :: y :: w) red =
        cons-is-reduced (flip x) (flip y) (Word-flip w)
          (flip2-is-reduced x y (head2-is-reduced x y w red))
          (Word-flip-is-reduced (y :: w) (tail-is-reduced x (y :: w) red))

    rw-inv : ReducedWord → ReducedWord
    rw-inv (w , red) = reverse (Word-flip w) , reverse-is-reduced (Word-flip w) (Word-flip-is-reduced w red)

    abstract
      rw-inv-l-lemma : ∀ w₁ x w₂ (red₂ : is-reduced (x :: w₂)) (red₂' : is-reduced w₂)
        →  rw-++' (w₁ ++ (flip x :: nil)) ((x :: w₂) , red₂)
        == rw-++' w₁ (w₂ , red₂')
      rw-inv-l-lemma nil (inl x) w₂ _ _ with dec x x
      rw-inv-l-lemma nil (inl x) w₂ _ _ | inl p = ReducedWord=-out idp
      rw-inv-l-lemma nil (inl x) w₂ _ _ | inr ¬p = ⊥-rec (¬p idp)
      rw-inv-l-lemma nil (inr x) w₂ _ _ with dec x x
      rw-inv-l-lemma nil (inr x) w₂ _ _ | inl p = ReducedWord=-out idp
      rw-inv-l-lemma nil (inr x) w₂ _ _ | inr ¬p = ⊥-rec (¬p idp)
      rw-inv-l-lemma (x :: w₁) y w₂ red₂ red₂' =
        ap (rw-cons x) (rw-inv-l-lemma w₁ y w₂ red₂ red₂')

      rw-inv-l' : ∀ w (red : is-reduced w)
        → rw-++' (reverse (Word-flip w)) (w , red) == nil , lift tt
      rw-inv-l' nil _ = idp
      rw-inv-l' (x :: w) red =
          rw-inv-l-lemma (reverse (Word-flip w)) x w red (tail-is-reduced x w red)
        ∙ rw-inv-l' w (tail-is-reduced x w red)

      suffix-is-reduced : ∀ w₁ w₂ → is-reduced (w₁ ++ w₂) → is-reduced w₂
      suffix-is-reduced nil w₂ red = red
      suffix-is-reduced (x :: w₁) w₂ red = suffix-is-reduced w₁ w₂ $ tail-is-reduced x (w₁ ++ w₂) red

      rw-inv-r-lemma-step : ∀ x w₂ (red₂ : is-reduced (flip x :: w₂)) (red₂' : is-reduced w₂)
        →  rw-cons x ((flip x :: w₂) , red₂)
        == w₂ , red₂'
      rw-inv-r-lemma-step (inl x) w₂ red₂ red₂' with dec x x
      rw-inv-r-lemma-step (inl x) w₂ red₂ red₂' | inl p = ReducedWord=-out idp
      rw-inv-r-lemma-step (inl x) w₂ red₂ red₂' | inr ¬p = ⊥-rec (¬p idp)
      rw-inv-r-lemma-step (inr x) w₂ red₂ red₂' with dec x x
      rw-inv-r-lemma-step (inr x) w₂ red₂ red₂' | inl p = ReducedWord=-out idp
      rw-inv-r-lemma-step (inr x) w₂ red₂ red₂' | inr ¬p = ⊥-rec (¬p idp)

      rw-inv-r-lemma : ∀ w₁ w₂ (red₁₂ : is-reduced (reverse (Word-flip w₁) ++ w₂)) (red₂ : is-reduced w₂)
        →  rw-++' w₁ ((reverse (Word-flip w₁) ++ w₂) , red₁₂)
        == w₂ , red₂
      rw-inv-r-lemma nil _ _ _ = ReducedWord=-out idp
      rw-inv-r-lemma (x :: w₁) w₂ red₁₂ red₂ =
          ap (rw-cons x)
            ( ap (rw-++' w₁) (ReducedWord=-out mediating-path)
            ∙ rw-inv-r-lemma w₁ (flip x :: w₂) red₁₂' red₂')
        ∙ rw-inv-r-lemma-step x w₂ red₂' red₂
        where
          mediating-path : reverse (Word-flip (x :: w₁)) ++ w₂
                        == reverse (Word-flip w₁) ++ (flip x :: w₂)
          mediating-path = ++-assoc (reverse (Word-flip w₁)) (flip x :: nil) w₂

          red₁₂' : is-reduced (reverse (Word-flip w₁) ++ (flip x :: w₂))
          red₁₂' = transport is-reduced mediating-path red₁₂

          red₂' : is-reduced (flip x :: w₂)
          red₂' = suffix-is-reduced (reverse (Word-flip w₁)) (flip x :: w₂) red₁₂'

      rw-inv-r : ∀ rw → rw-++ rw (rw-inv rw) == nil , lift tt
      rw-inv-r (w , red) =
          ap (rw-++' w) (ReducedWord=-out mediating-path)
        ∙ rw-inv-r-lemma w nil
            (transport is-reduced mediating-path (reverse-is-reduced (Word-flip w) (Word-flip-is-reduced w red)))
            (lift tt)
        where
          mediating-path : reverse (Word-flip w) == reverse (Word-flip w) ++ nil
          mediating-path = ! $ ++-unit-r _

  ReducedWord-group-struct : GroupStructure ReducedWord
  ReducedWord-group-struct = record
    { ident = nil , lift tt
    ; inv = rw-inv
    ; comp = rw-++
    ; unit-l = λ _ → idp
    ; unit-r = uncurry rw-++-unit-r'
    ; assoc = λ rw → rw-++-assoc' (fst rw)
    ; inv-r = rw-inv-r
    ; inv-l = uncurry rw-inv-l'
    }

  ReducedWord-group : Group i
  ReducedWord-group = group _ ReducedWord-is-set ReducedWord-group-struct

  private
    abstract
      QuotWordRel-cons : ∀ x w₂ (red₂ : is-reduced w₂)
        → QuotWordRel (x :: w₂) (fst (rw-cons x (w₂ , red₂)))
      QuotWordRel-cons x nil _ = qwr-refl idp
      QuotWordRel-cons (inl x) (inl y :: w) _ = qwr-refl idp
      QuotWordRel-cons (inl x) (inr y :: w) _ with dec x y
      QuotWordRel-cons (inl x) (inr y :: w) _ | inl x=y rewrite x=y = qwr-flip (inl y) w
      QuotWordRel-cons (inl x) (inr y :: w) _ | inr x≠y = qwr-refl idp
      QuotWordRel-cons (inr x) (inl y :: w) _ with dec x y
      QuotWordRel-cons (inr x) (inl y :: w) _ | inl x=y rewrite x=y = qwr-flip (inr y) w
      QuotWordRel-cons (inr x) (inl y :: w) _ | inr x≠y = qwr-refl idp
      QuotWordRel-cons (inr x) (inr y :: w) _ = qwr-refl idp

      QuotWordRel-++ : ∀ w₁ rw₂
        → QuotWordRel (w₁ ++ fst rw₂) (fst (rw-++' w₁ rw₂))
      QuotWordRel-++ nil _ = qwr-refl idp
      QuotWordRel-++ (x :: w₁) rw₂ =
        qwr-trans (qwr-cons x (QuotWordRel-++ w₁ rw₂)) $
        uncurry (QuotWordRel-cons x) (rw-++' w₁ rw₂)

  -- freeness
  ReducedWord-to-FreeGroup : ReducedWord-group →ᴳ FreeGroup A
  ReducedWord-to-FreeGroup = group-hom (λ rw → qw[ fst rw ])
    (λ rw₁ rw₂ → ! $ quot-rel $ QuotWordRel-++ (fst rw₁) rw₂)

  private
    abstract
      reduce-emap : ∀ {w₁ w₂} → QuotWordRel w₁ w₂ → reduce w₁ == reduce w₂
      reduce-emap (qwr-refl p) = ap reduce p
      reduce-emap (qwr-trans qwr₁ qwr₂) = reduce-emap qwr₁ ∙ reduce-emap qwr₂
      reduce-emap (qwr-sym qwr) = ! (reduce-emap qwr)
      reduce-emap (qwr-cons x qwr) = ap (rw-cons x) (reduce-emap qwr)
      reduce-emap (qwr-flip x w) = rw-cons-cons-flip x (reduce w)

    to = GroupHom.f ReducedWord-to-FreeGroup

    from : QuotWord A → ReducedWord
    from = QuotWord-rec ReducedWord-is-set reduce reduce-emap

    abstract
      QuotWordRel-reduce : ∀ w
        → QuotWordRel w (fst (reduce w))
      QuotWordRel-reduce nil = qwr-refl idp
      QuotWordRel-reduce (x :: w) =
        qwr-trans (qwr-cons x (QuotWordRel-reduce w)) $
        uncurry (QuotWordRel-cons x) (reduce w)

      to-from : ∀ qw → to (from qw) == qw
      to-from = QuotWord-elim (λ _ → =-preserves-set QuotWord-is-set)
        (λ w → ! $ quot-rel $ QuotWordRel-reduce w)
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _))

      from-to : ∀ rw → from (to rw) == rw
      from-to = uncurry rw-++-unit-r'

  ReducedWord-iso-FreeGroup : ReducedWord-group ≃ᴳ FreeGroup A
  ReducedWord-iso-FreeGroup = ReducedWord-to-FreeGroup , is-eq to from to-from from-to
