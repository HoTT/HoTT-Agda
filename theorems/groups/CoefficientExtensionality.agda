{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.CoefficientExtensionality where

module _ {i} {A : Type i} (dec : has-dec-eq A) where

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
  FormalSum-coef = FormalSum-rec Word-coef (λ r → λ= $ FormalSum-coef-rel r)

  -- Theorem : if coef w a == 0 then FormalSumRel w nil

  private
    abstract
      Word-exp-succ : ∀ (a : A) z → FormalSumRel (inl a :: Word-exp a z) (Word-exp a (succ z))
      Word-exp-succ a (pos _) = fsr-refl idp
      Word-exp-succ a (negsucc 0) = fsr-flip (inl a) nil
      Word-exp-succ a (negsucc (S n)) = fsr-flip (inl a) (Word-exp a (negsucc n))

      Word-exp-pred : ∀ (a : A) z → FormalSumRel (inr a :: Word-exp a z) (Word-exp a (pred z))
      Word-exp-pred a (pos 0) = fsr-refl idp
      Word-exp-pred a (pos (S n)) = fsr-flip (inr a) (Word-exp a (pos n))
      Word-exp-pred a (negsucc _) = fsr-refl idp

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
        fsr : FormalSumRel w (Word-exp a left-exponent ++ right-list)

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
                        (FormalSumRel-cong-++-l (Word-exp-succ a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      ... | inr b≠a = record {
        left-exponent = left-exponent;
        left-captures-all = Word-coef-inl-neq b≠a w ∙ left-captures-all;
        right-list = inl b :: right-list;
        right-shorter = ≤-ap-S right-shorter;
        fsr = fsr-trans (fsr-cons (inl b) fsr) $
          fsr-sym (FormalSumRel-swap1 (inl b) (Word-exp a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      collect-split a (inr b :: w) idp with dec b a
      ... | inl b=a = record {
        left-exponent = pred left-exponent;
        left-captures-all = Word-coef-inr-eq b=a w ∙ ap pred left-captures-all;
        right-list = right-list;
        right-shorter = ≤-trans right-shorter (inr ltS);
        fsr = fsr-trans (fsr-refl (ap (λ a → inr a :: w) b=a)) $
              fsr-trans (fsr-cons (inr a) fsr) $
                        (FormalSumRel-cong-++-l (Word-exp-pred a left-exponent) right-list)}
        where open CollectSplitIH (collect-split a w idp)
      ... | inr b≠a = record {
        left-exponent = left-exponent;
        left-captures-all = Word-coef-inr-neq b≠a w ∙ left-captures-all;
        right-list = inr b :: right-list;
        right-shorter = ≤-ap-S right-shorter;
        fsr = fsr-trans (fsr-cons (inr b) fsr) $
          fsr-sym (FormalSumRel-swap1 (inr b) (Word-exp a left-exponent) right-list)}
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
            fsr-trans (fsr-refl (ap (λ e → inl a :: Word-exp a e ++ right-list) left-exponent-is-minus-one)) $
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
            fsr-trans (fsr-refl (ap (λ e → inr a :: Word-exp a e ++ right-list) left-exponent-is-one)) $
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
      (λ w₁ → FormalSum-elim
        (λ w₂ → FormalSum-coef-ext' w₁ w₂)
        (λ _ → prop-has-all-paths-↓))
      (λ _ → prop-has-all-paths-↓)

  has-finite-support : (A → ℤ) → Type i
  has-finite-support f = Σ (FormalSum A) λ fs → ∀ a → f a == FormalSum-coef fs a

module _ {i} {A : Type i} {dec : has-dec-eq A} where

  abstract
    has-finite-support-is-prop : ∀ f → is-prop (has-finite-support dec f)
    has-finite-support-is-prop f = all-paths-is-prop
      λ{(fs₁ , match₁) (fs₂ , match₂) → pair=
        (FormalSum-coef-ext dec fs₁ fs₂ λ a → ! (match₁ a) ∙ match₂ a)
        prop-has-all-paths-↓}

module _ where

  private
    abstract
      Word-coef-exp-diag-pos : ∀ {I} (<I : Fin I) n →
        Word-coef Fin-has-dec-eq (Word-exp <I (pos n)) <I == pos n
      Word-coef-exp-diag-pos <I O = idp
      Word-coef-exp-diag-pos <I (S n) with Fin-has-dec-eq <I <I
      ... | inl _ = ap succ (Word-coef-exp-diag-pos <I n)
      ... | inr ¬p = ⊥-rec (¬p idp)

      Word-coef-exp-diag-negsucc : ∀ {I} (<I : Fin I) n →
        Word-coef Fin-has-dec-eq (Word-exp <I (negsucc n)) <I == negsucc n
      Word-coef-exp-diag-negsucc <I O with Fin-has-dec-eq <I <I
      ... | inl _ = idp
      ... | inr ¬p = ⊥-rec (¬p idp)
      Word-coef-exp-diag-negsucc <I (S n) with Fin-has-dec-eq <I <I
      ... | inl _ = ap pred (Word-coef-exp-diag-negsucc <I n)
      ... | inr ¬p = ⊥-rec (¬p idp)

      Word-coef-exp-diag : ∀ {I} (<I : Fin I) z →
        Word-coef Fin-has-dec-eq (Word-exp <I z) <I == z
      Word-coef-exp-diag <I (pos n) = Word-coef-exp-diag-pos <I n
      Word-coef-exp-diag <I (negsucc n) = Word-coef-exp-diag-negsucc <I n

      Word-coef-exp-≠-pos : ∀ {I} {<I <I' : Fin I} (_ : <I ≠ <I') n →
        Word-coef Fin-has-dec-eq (Word-exp <I (pos n)) <I' == 0
      Word-coef-exp-≠-pos _ O = idp
      Word-coef-exp-≠-pos {<I = <I} {<I'} neq (S n) with Fin-has-dec-eq <I <I'
      ... | inl p = ⊥-rec (neq p)
      ... | inr ¬p = Word-coef-exp-≠-pos neq n

      Word-coef-exp-≠-negsucc : ∀ {I} {<I <I' : Fin I} (_ : <I ≠ <I') n →
        Word-coef Fin-has-dec-eq (Word-exp <I (negsucc n)) <I' == 0
      Word-coef-exp-≠-negsucc {<I = <I} {<I'} neq O with Fin-has-dec-eq <I <I'
      ... | inl p = ⊥-rec (neq p)
      ... | inr ¬p = idp
      Word-coef-exp-≠-negsucc {<I = <I} {<I'} neq (S n) with Fin-has-dec-eq <I <I'
      ... | inl p = ⊥-rec (neq p)
      ... | inr ¬p = Word-coef-exp-≠-negsucc neq n

      Word-coef-exp-≠ : ∀ {I} {<I <I' : Fin I} (_ : <I ≠ <I') z →
        Word-coef Fin-has-dec-eq (Word-exp <I z) <I' == 0
      Word-coef-exp-≠ neq (pos n) = Word-coef-exp-≠-pos neq n
      Word-coef-exp-≠ neq (negsucc n) = Word-coef-exp-≠-negsucc neq n

    Word-sum' : ∀ (I : ℕ) {A : Type₀} (F : Fin I → A) (f : Fin I → ℤ) → Word A
    Word-sum' 0 F f = nil
    Word-sum' (S I) F f = Word-sum' I (F ∘ Fin-S) (f ∘ Fin-S) ++ Word-exp (F (I , ltS)) (f (I , ltS))

    Word-sum : ∀ {I : ℕ} (f : Fin I → ℤ) → Word (Fin I)
    Word-sum {I} f = Word-sum' I (idf (Fin I)) f

    abstract
      Word-coef-sum'-late : ∀ n m (I : ℕ) (f : Fin I → ℤ)
        → Word-coef Fin-has-dec-eq (Word-sum' I (Fin-S^' (S n) ∘ Fin-S^' m) f) (Fin-S^' n (ℕ-S^' m I , ltS)) == 0
      Word-coef-sum'-late n m 0 f = idp
      Word-coef-sum'-late n m (S I) f =
        Word-coef Fin-has-dec-eq
          (Word-sum' I (Fin-S^' (S n) ∘ Fin-S^' (S m)) (f ∘ Fin-S) ++ Word-exp (Fin-S^' (S n) (Fin-S^' m (I , ltS))) (f (I , ltS)))
          (Fin-S^' n (ℕ-S^' (S m) I , ltS))
          =⟨ Word-coef-++ Fin-has-dec-eq
              (Word-sum' I (Fin-S^' (S n) ∘ Fin-S^' (S m)) (f ∘ Fin-S))
              (Word-exp (Fin-S^' (S n) (Fin-S^' m (I , ltS))) (f (I , ltS)))
              (Fin-S^' n (ℕ-S^' (S m) I , ltS)) ⟩
        Word-coef Fin-has-dec-eq (Word-sum' I (Fin-S^' (S n) ∘ Fin-S^' (S m)) (f ∘ Fin-S)) (Fin-S^' n (ℕ-S^' (S m) I , ltS))
        ℤ+
        Word-coef Fin-has-dec-eq (Word-exp (Fin-S^' (S n) (Fin-S^' m (I , ltS))) (f (I , ltS))) (Fin-S^' n (ℕ-S^' (S m) I , ltS))
          =⟨ ap2 _ℤ+_
              (Word-coef-sum'-late n (S m) I (f ∘ Fin-S))
              (Word-coef-exp-≠ (Fin-S^'-≠ n (ltSR≠ltS _)) (f (I , ltS))) ⟩
        0
          =∎

      Word-coef-sum' : ∀ n {I} (f : Fin I → ℤ) <I
        → Word-coef Fin-has-dec-eq (Word-sum' I (Fin-S^' n) f) (Fin-S^' n <I) == f <I
      Word-coef-sum' n f (I , ltS) =
        Word-coef Fin-has-dec-eq
          (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S) ++ Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS)))
          (Fin-S^' n (I , ltS))
          =⟨ Word-coef-++ Fin-has-dec-eq
              (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S))
              (Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS)))
              (Fin-S^' n (I , ltS)) ⟩
        Word-coef Fin-has-dec-eq (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S)) (Fin-S^' n (I , ltS))
        ℤ+
        Word-coef Fin-has-dec-eq (Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS))) (Fin-S^' n (I , ltS))
          =⟨ ap2 _ℤ+_
              (Word-coef-sum'-late n 0 I (f ∘ Fin-S))
              (Word-coef-exp-diag (Fin-S^' n (I , ltS)) (f (I , ltS))) ⟩
        f (I , ltS)
          =∎
      Word-coef-sum' n {I = S I} f (m , ltSR m<I) =
        Word-coef Fin-has-dec-eq
          (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S) ++ Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS)))
          (Fin-S^' (S n) (m , m<I))
          =⟨ Word-coef-++ Fin-has-dec-eq
              (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S))
              (Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS)))
              (Fin-S^' (S n) (m , m<I)) ⟩
        Word-coef Fin-has-dec-eq (Word-sum' I (Fin-S^' (S n)) (f ∘ Fin-S)) (Fin-S^' (S n) (m , m<I))
        ℤ+
        Word-coef Fin-has-dec-eq (Word-exp (Fin-S^' n (I , ltS)) (f (I , ltS))) (Fin-S^' (S n) (m , m<I))
          =⟨ ap2 _ℤ+_
              (Word-coef-sum' (S n) {I} (f ∘ Fin-S) (m , m<I))
              (Word-coef-exp-≠ (Fin-S^'-≠ n (ltS≠ltSR (m , m<I))) (f (I , ltS))) ⟩
        f (m , ltSR m<I) ℤ+ 0
          =⟨ ℤ+-unit-r _ ⟩
        f (m , ltSR m<I)
          =∎

  FormalSum-sum' : ∀ n (I : ℕ) (f : Fin I → ℤ) → FormalSum (Fin (ℕ-S^' n I))
  FormalSum-sum' n I f =
    Group.sum (FreeAbGroup.grp (Fin (ℕ-S^' n I)))
      (λ <I → Group.exp (FreeAbGroup.grp (Fin (ℕ-S^' n I))) fs[ inl (Fin-S^' n <I) :: nil ] (f <I))

  FormalSum-sum : ∀ {I : ℕ} (f : Fin I → ℤ) → FormalSum (Fin I)
  FormalSum-sum {I} = FormalSum-sum' 0 I

  private
    abstract
      FormalSum-sum'-β : ∀ n (I : ℕ) (f : Fin I → ℤ)
        → FormalSum-sum' n I f == fs[ Word-sum' I (Fin-S^' n) f ]
      FormalSum-sum'-β n O f = idp
      FormalSum-sum'-β n (S I) f =
        ap2 (Group.comp (FreeAbGroup.grp (Fin (ℕ-S^' (S n) I))))
          (FormalSum-sum'-β (S n) I (f ∘ Fin-S))
          (! (FormalSumRel-pres-exp (Fin-S^' n (I , ltS)) (f (I , ltS))))

  Fin→-has-finite-support : ∀ {I} (f : Fin I → ℤ) → has-finite-support Fin-has-dec-eq f
  Fin→-has-finite-support {I} f = FormalSum-sum f , lemma
    where abstract lemma = λ <I → ! (ap (λ fs → FormalSum-coef Fin-has-dec-eq fs <I) (FormalSum-sum'-β 0 I f) ∙ Word-coef-sum' 0 f <I)
