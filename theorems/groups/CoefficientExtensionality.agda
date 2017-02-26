{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.CoefficientExtensionality {i} {A : Type i} where

module _ (dec : has-dec-eq A) where

  Word-coef : Word A → (A → ℤ)
  Word-coef nil a = 0
  Word-coef (inl a' :: w) a with dec a' a
  Word-coef (inl a' :: w) a | inl a'=a = succ $ Word-coef w a
  Word-coef (inl a' :: w) a | inr a'≠a = Word-coef w a
  Word-coef (inr a' :: w) a with dec a' a
  Word-coef (inr a' :: w) a | inl a'=a = pred $ Word-coef w a
  Word-coef (inr a' :: w) a | inr a'≠a = Word-coef w a

  abstract
    Word-coef-++ : ∀ w₁ w₂ a → Word-coef (w₁ ++ w₂) a
      == Word-coef w₁ a ℤ+ Word-coef w₂ a
    Word-coef-++ nil w₂ a = idp
    Word-coef-++ (inl a' :: w₁) w₂ a with dec a' a
    Word-coef-++ (inl a' :: w₁) w₂ a | inl a'=a =
        ap succ (Word-coef-++ w₁ w₂ a)
      ∙ ! (succ-+ (Word-coef w₁ a) (Word-coef w₂ a))
    Word-coef-++ (inl a' :: w₁) w₂ a | inr a'≠a = Word-coef-++ w₁ w₂ a
    Word-coef-++ (inr a' :: w₁) w₂ a with dec a' a
    Word-coef-++ (inr a' :: w₁) w₂ a | inl a'=a =
        ap pred (Word-coef-++ w₁ w₂ a)
      ∙ ! (pred-+ (Word-coef w₁ a) (Word-coef w₂ a))
    Word-coef-++ (inr a' :: w₁) w₂ a | inr a'≠a = Word-coef-++ w₁ w₂ a

    Word-coef-flip : ∀ w a → Word-coef (Word-flip w) a == ℤ~ (Word-coef w a)
    Word-coef-flip nil a = idp
    Word-coef-flip (inl a' :: w) a with dec a' a
    Word-coef-flip (inl a' :: w) a | inl a'=a =
        ap pred (Word-coef-flip w a) ∙ ! (ℤ~-succ (Word-coef w a))
    Word-coef-flip (inl a' :: w) a | inr a'≠a = Word-coef-flip w a
    Word-coef-flip (inr a' :: w) a with dec a' a
    Word-coef-flip (inr a' :: w) a | inl a'=a =
        ap succ (Word-coef-flip w a) ∙ ! (ℤ~-pred (Word-coef w a))
    Word-coef-flip (inr a' :: w) a | inr a'≠a = Word-coef-flip w a

  private
    abstract
      FormalSum-coef-rel : {w₁ w₂ : Word A} → FormalSumRel w₁ w₂
        → ∀ a → Word-coef w₁ a == Word-coef w₂ a
      FormalSum-coef-rel (fsr-refl p) a = ap (λ w → Word-coef w a) p
      FormalSum-coef-rel (fsr-trans fwr₁ fwr₂) a = (FormalSum-coef-rel fwr₁ a) ∙ (FormalSum-coef-rel fwr₂ a)
      FormalSum-coef-rel (fsr-sym fsr) a = ! $ FormalSum-coef-rel fsr a
      FormalSum-coef-rel (fsr-cons x fwr) a =
          Word-coef-++ (x :: nil) _ a
        ∙ ap (Word-coef (x :: nil) a ℤ+_) (FormalSum-coef-rel fwr a)
        ∙ ! (Word-coef-++ (x :: nil) _ a)
      FormalSum-coef-rel (fsr-swap x y w) a =
          Word-coef-++ (x :: y :: nil) _ a
        ∙ ap (_ℤ+ Word-coef w a)
            ( Word-coef-++ (x :: nil) (y :: nil) a
            ∙ ℤ+-comm (Word-coef (x :: nil) a) (Word-coef (y :: nil) a)
            ∙ ! (Word-coef-++ (y :: nil) (x :: nil) a))
        ∙ ! (Word-coef-++ (y :: x :: nil) _ a)
      FormalSum-coef-rel (fsr-flip x w) a =
          Word-coef-++ (x :: flip x :: nil) w a
        ∙ ap (_ℤ+ Word-coef w a)
            ( Word-coef-++ (x :: nil) (flip x :: nil) a
            ∙ ap (Word-coef (x :: nil) a ℤ+_) (Word-coef-flip (x :: nil) a)
            ∙ ℤ~-inv-r (Word-coef (x :: nil) a) )
        ∙ ℤ+-unit-l (Word-coef w a)

  FormalSum-coef : FormalSum A → (A → ℤ)
  FormalSum-coef = FormalSum-rec (→-is-set ℤ-is-set) Word-coef (λ r → λ= $ FormalSum-coef-rel r)

  -- Theorem : if coef w a == 0 then FormalSumRel w nil

  private
    exp : A → ℤ → Word A
    exp a (pos 0) = nil
    exp a (pos (S n)) = inl a :: exp a (pos n)
    exp a (negsucc 0) = inr a :: nil
    exp a (negsucc (S n)) = inr a :: exp a (negsucc n)

    abstract
      exp-succ : ∀ a z → FormalSumRel (inl a :: exp a z) (exp a (succ z))
      exp-succ a (pos _) = fsr-refl idp
      exp-succ a (negsucc 0) = fsr-flip (inl a) nil
      exp-succ a (negsucc (S n)) = fsr-flip (inl a) (exp a (negsucc n))

      exp-pred : ∀ a z → FormalSumRel (inr a :: exp a z) (exp a (pred z))
      exp-pred a (pos 0) = fsr-refl idp
      exp-pred a (pos (S n)) = fsr-flip (inr a) (exp a (pos n))
      exp-pred a (negsucc _) = fsr-refl idp

      Word-coef-inl-eq : ∀ {a b} (p : b == a) w
        → Word-coef (inl b :: w) a == succ (Word-coef w a)
      Word-coef-inl-eq {a} {b} p w with dec b a
      Word-coef-inl-eq {a} {b} p w | inl _ = idp
      Word-coef-inl-eq {a} {b} p w | inr ¬p = ⊥-rec (¬p p)

      Word-coef-inr-eq : ∀ {a b} (p : b == a) w
        → Word-coef (inr b :: w) a == pred (Word-coef w a)
      Word-coef-inr-eq {a} {b} p w with dec b a
      Word-coef-inr-eq {a} {b} p w | inl _ = idp
      Word-coef-inr-eq {a} {b} p w | inr ¬p = ⊥-rec (¬p p)

      Word-coef-inl-neq : ∀ {a b} (p : b ≠ a) w
        → Word-coef (inl b :: w) a == Word-coef w a
      Word-coef-inl-neq {a} {b} ¬p w with dec b a
      Word-coef-inl-neq {a} {b} ¬p w | inl p = ⊥-rec (¬p p)
      Word-coef-inl-neq {a} {b} ¬p w | inr _ = idp

      Word-coef-inr-neq : ∀ {a b} (p : b ≠ a) w
        → Word-coef (inr b :: w) a == Word-coef w a
      Word-coef-inr-neq {a} {b} ¬p w with dec b a
      Word-coef-inr-neq {a} {b} ¬p w | inl p = ⊥-rec (¬p p)
      Word-coef-inr-neq {a} {b} ¬p w | inr _ = idp

    -- TODO maybe there is a better way to prove the final theorem?
    -- Here we are collecting all elements [inl a] and [inr a], and recurse on the rest.
    -- The [right-shorter] field makes sure that it is terminating.
    record CollectSplitIH (a : A) {n : ℕ} (w : Word A) (len : length w == n) : Type i where
      field
        left-exponent : ℤ
        left-captures-all : Word-coef w a == left-exponent
        right-list : Word A
        right-shorter : length right-list ≤ n
        fsr : FormalSumRel w (exp a left-exponent ++ right-list)

    abstract
      collect-split : ∀ a {n} w (len=n : length w == n) → CollectSplitIH a w len=n
      collect-split a nil idp = record {
        left-exponent = 0;
        left-captures-all = idp;
        right-list = nil;
        right-shorter = inl idp;
        fsr = fsr-refl idp}
      collect-split a (inl b :: w) idp with dec b a
      ... | inl b=a = record {
        left-exponent = succ left-exponent;
        left-captures-all = Word-coef-inl-eq b=a w ∙ ap succ left-captures-all;
        right-list = right-list;
        right-shorter = ≤-trans right-shorter (inr ltS);
        fsr = fsr-trans (fsr-refl (ap (λ a → inl a :: w) b=a)) $
              fsr-trans (fsr-cons (inl a) fsr) $
                        (FormalSumRel-cong-++-l (exp-succ a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      ... | inr b≠a = record {
        left-exponent = left-exponent;
        left-captures-all = Word-coef-inl-neq b≠a w ∙ left-captures-all;
        right-list = inl b :: right-list;
        right-shorter = ≤-ap-S right-shorter;
        fsr = fsr-trans (fsr-cons (inl b) fsr) $
          fsr-sym (FormalSumRel-swap1 (inl b) (exp a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      collect-split a (inr b :: w) idp with dec b a
      ... | inl b=a = record {
        left-exponent = pred left-exponent;
        left-captures-all = Word-coef-inr-eq b=a w ∙ ap pred left-captures-all;
        right-list = right-list;
        right-shorter = ≤-trans right-shorter (inr ltS);
        fsr = fsr-trans (fsr-refl (ap (λ a → inr a :: w) b=a)) $
              fsr-trans (fsr-cons (inr a) fsr) $
                        (FormalSumRel-cong-++-l (exp-pred a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      ... | inr b≠a = record {
        left-exponent = left-exponent;
        left-captures-all = Word-coef-inr-neq b≠a w ∙ left-captures-all;
        right-list = inr b :: right-list;
        right-shorter = ≤-ap-S right-shorter;
        fsr = fsr-trans (fsr-cons (inr b) fsr) $
          fsr-sym (FormalSumRel-swap1 (inr b) (exp a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)

      -- We simulate strong induction by recursing on both [m] and [n≤m].
      -- We could develop a general framework for strong induction but I am lazy. -Favonia
      zero-coef-is-ident' : ∀ {m n} (n≤m : n ≤ m) (w : Word A) (len : length w == n)
        → (∀ a → Word-coef w a == 0) → FormalSumRel w nil
      zero-coef-is-ident' (inr ltS) w len zero-coef
        = zero-coef-is-ident' (inl idp) w len zero-coef
      zero-coef-is-ident' (inr (ltSR lt)) w len zero-coef
        = zero-coef-is-ident' (inr lt) w len zero-coef
      zero-coef-is-ident' {m = O} (inl idp) nil _ _ = fsr-refl idp
      zero-coef-is-ident' {m = O} (inl idp) (_ :: _) len _ = ⊥-rec $ ℕ-S≠O _ len
      zero-coef-is-ident' {m = S m} (inl idp) nil len _ = ⊥-rec $ ℕ-S≠O _ (! len)
      zero-coef-is-ident' {m = S m} (inl idp) (inl a :: w) len zero-coef =
        fsr-trans whole-is-right (zero-coef-is-ident' right-shorter right-list idp right-zero-coef)
        where
          open CollectSplitIH (collect-split a w (ℕ-S-is-inj _ _ len))
          left-exponent-is-minus-one : left-exponent == -1
          left-exponent-is-minus-one = succ-is-inj left-exponent -1 $
            ap succ (! left-captures-all) ∙ ! (Word-coef-inl-eq idp w) ∙ zero-coef a

          whole-is-right : FormalSumRel (inl a :: w) right-list
          whole-is-right =
            fsr-trans (fsr-cons (inl a) fsr) $
            fsr-trans (fsr-refl (ap (λ e → inl a :: exp a e ++ right-list) left-exponent-is-minus-one)) $
                      fsr-flip (inl a) right-list

          right-zero-coef : ∀ a' → Word-coef right-list a' == 0
          right-zero-coef a' = ! (FormalSum-coef-rel whole-is-right a') ∙ zero-coef a'
      zero-coef-is-ident' {m = S m} (inl idp) (inr a :: w) len zero-coef =
        fsr-trans whole-is-right (zero-coef-is-ident' right-shorter right-list idp right-zero-coef)
        where
          open CollectSplitIH (collect-split a w (ℕ-S-is-inj _ _ len))
          left-exponent-is-one : left-exponent == 1
          left-exponent-is-one = pred-is-inj left-exponent 1 $
            ap pred (! left-captures-all) ∙ ! (Word-coef-inr-eq idp w) ∙ zero-coef a

          whole-is-right : FormalSumRel (inr a :: w) right-list
          whole-is-right =
            fsr-trans (fsr-cons (inr a) fsr) $
            fsr-trans (fsr-refl (ap (λ e → inr a :: exp a e ++ right-list) left-exponent-is-one)) $
                      fsr-flip (inr a) right-list

          right-zero-coef : ∀ a' → Word-coef right-list a' == 0
          right-zero-coef a' = ! (FormalSum-coef-rel whole-is-right a') ∙ zero-coef a'

      zero-coef-is-ident : ∀ (w : Word A)
        → (∀ a → Word-coef w a == 0)
        → FormalSumRel w nil
      zero-coef-is-ident w = zero-coef-is-ident' (inl idp) w idp

  abstract
    FormalSum-coef-ext' : ∀ w₁ w₂
      → (∀ a → Word-coef w₁ a == Word-coef w₂ a)
      → fs[ w₁ ] == fs[ w₂ ]
    FormalSum-coef-ext' w₁ w₂ same-coef = G.inv-is-inj fs[ w₁ ] fs[ w₂ ] $
      G.inv-unique-l (G.inv fs[ w₂ ]) fs[ w₁ ] $ quot-rel $
      zero-coef-is-ident (Word-flip w₂ ++ w₁)
        (λ a → Word-coef-++ (Word-flip w₂) w₁ a
             ∙ ap2 _ℤ+_ (Word-coef-flip w₂ a) (same-coef a)
             ∙ ℤ~-inv-l (Word-coef w₂ a))
      where module G = FreeAbGroup A

    FormalSum-coef-ext : ∀ fs₁ fs₂
      → (∀ a → FormalSum-coef fs₁ a == FormalSum-coef fs₂ a)
      → fs₁ == fs₂
    FormalSum-coef-ext = FormalSum-elim
      (λ fs₁ → Π-is-set λ fs₂ → →-is-set $ =-preserves-set FormalSum-is-set)
      (λ w₁ → FormalSum-elim
        (λ fs₂ → →-is-set $ =-preserves-set FormalSum-is-set)
        (λ w₂ → FormalSum-coef-ext' w₁ w₂)
        (λ _ → prop-has-all-paths-↓ (→-is-prop $ FormalSum-is-set _ _)))
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → →-is-prop $ FormalSum-is-set _ _))

  has-finite-supports : (A → ℤ) → Type i
  has-finite-supports f = Σ (FormalSum A) λ fs → ∀ a → f a == FormalSum-coef fs a

module _ {dec : has-dec-eq A} where

  abstract
    has-finite-supports-is-prop : ∀ f → is-prop (has-finite-supports dec f)
    has-finite-supports-is-prop f = all-paths-is-prop
      λ{(fs₁ , match₁) (fs₂ , match₂) → pair=
        (FormalSum-coef-ext dec fs₁ fs₂ λ a → ! (match₁ a) ∙ match₂ a)
        (prop-has-all-paths-↓ $ Π-is-prop λ _ → ℤ-is-set _ _)}
