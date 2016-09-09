{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Nat
open import lib.types.Int
open import lib.types.List
open import lib.types.SetQuotient
open import lib.groups.Homomorphisms

-- TODO 1. Get rid of coeffients.
-- TODO 2. Use another quotient relations without [dec].
-- TODO 3. Define [FormalSum] as an abstract type.

module lib.groups.FreeAbelianGroup {i} where

PreFormalSum : Type i → Type i
PreFormalSum A = List (ℤ × A)

module _ {A : Type i} where

  flip-pre : PreFormalSum A → PreFormalSum A
  flip-pre = map λ{(z , a) → (ℤ~ z , a)}

module _ {A : Type i} (dec : has-dec-eq A) where

  coef-pre : PreFormalSum A → (A → ℤ)
  coef-pre l a = ℤsum $ map fst $ filter (λ{(_ , a') → dec a' a}) l

  -- Extensional equality
  formal-sum-rel : Rel (PreFormalSum A) i
  formal-sum-rel l₁ l₂ = ∀ a → coef-pre l₁ a == coef-pre l₂ a

  -- The quotient
  FormalSum : Type i
  FormalSum = SetQuotient formal-sum-rel

  -- Properties of [coef-pre]
  coef-pre-++ : ∀ l₁ l₂ a
    → coef-pre (l₁ ++ l₂) a == coef-pre l₁ a ℤ+ coef-pre l₂ a
  coef-pre-++ nil              l₂ a = idp
  coef-pre-++ ((z , a') :: l₁) l₂ a with dec a' a
  ... | inl _ = ap (z ℤ+_) (coef-pre-++ l₁ l₂ a)
              ∙ ! (ℤ+-assoc z (coef-pre l₁ a) (coef-pre l₂ a))
  ... | inr _ = coef-pre-++ l₁ l₂ a

  coef-pre-matching : ∀ z {a x} (p : x == a) l
    → coef-pre ((z , x) :: l) a == z ℤ+ coef-pre l a
  coef-pre-matching z {a} {x} p l with dec x a
  ... | inl _ = idp
  ... | inr p⊥ = ⊥-rec (p⊥ p)

  coef-pre-flip : ∀ l a
    → coef-pre (flip-pre l) a == ℤ~ (coef-pre l a)
  coef-pre-flip nil a = idp
  coef-pre-flip ((z , a') :: l) a with dec a' a
  ... | inl _ = ap (ℤ~ z ℤ+_) (coef-pre-flip l a)
              ∙ ! (ℤ~-+ z (coef-pre l a))
  ... | inr _ = coef-pre-flip l a

module _ {A : Type i} {dec : has-dec-eq A} where

  coef : FormalSum dec → (A → ℤ)
  coef = SetQuot-rec (→-is-set ℤ-is-set) (coef-pre dec) λ=

  -- extensionality of formal sums.
  coef-ext : ∀ {fs₁ fs₂} → (∀ a → coef fs₁ a == coef fs₂ a) → fs₁ == fs₂
  coef-ext {fs₁} {fs₂} = ext' fs₁ fs₂ where
    ext' : ∀ fs₁ fs₂ → (∀ a → coef fs₁ a == coef fs₂ a) → fs₁ == fs₂
    ext' = SetQuot-elim
      (λ _ → Π-is-set λ _ → →-is-set $ =-preserves-set SetQuotient-is-set)
      (λ l₁ → SetQuot-elim
        (λ _ → →-is-set $ =-preserves-set SetQuotient-is-set)
        (λ l₂ r → quot-rel r)
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuotient-is-set _ _)))
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → SetQuotient-is-set _ _))

  infixl 80 _⊞_
  _⊞_ : FormalSum dec → FormalSum dec → FormalSum dec
  _⊞_ = SetQuot-rec
    (→-is-set SetQuotient-is-set)
    (λ l₁ → SetQuot-rec SetQuotient-is-set (q[_] ∘ (l₁ ++_))
      (λ {l₂} {l₂'} r → quot-rel λ a
        → coef-pre-++ dec l₁ l₂ a
        ∙ ap (coef-pre dec l₁ a ℤ+_) (r a)
        ∙ ! (coef-pre-++ dec l₁ l₂' a)))
    (λ {l₁} {l₁'} r → λ= $ SetQuot-elim
      (λ _ → =-preserves-set SetQuotient-is-set)
      (λ l₂ → quot-rel λ a
        → coef-pre-++ dec l₁ l₂ a
        ∙ ap (_ℤ+ coef-pre dec l₂ a) (r a)
        ∙ ! (coef-pre-++ dec l₁' l₂ a))
      (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _)))

  coef-⊞ : ∀ fs₁ fs₂ a → coef (fs₁ ⊞ fs₂) a == coef fs₁ a ℤ+ coef fs₂ a
  coef-⊞ = SetQuot-elim
    (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
    (λ l₁ → SetQuot-elim
      (λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
      (λ l₂ → coef-pre-++ dec l₁ l₂)
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → ℤ-is-set _ _)))
    (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → ℤ-is-set _ _))

  ⊟ : FormalSum dec → FormalSum dec
  ⊟ = SetQuot-rec SetQuotient-is-set (q[_] ∘ flip-pre)
    λ {l₁} {l₂} r → quot-rel λ a
      → coef-pre-flip dec l₁ a ∙ ap ℤ~ (r a) ∙ ! (coef-pre-flip dec l₂ a)

  coef-⊟ : ∀ fs a → coef (⊟ fs) a == ℤ~ (coef fs a)
  coef-⊟ = SetQuot-elim
    (λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
    (λ l a → coef-pre-flip dec l a)
    (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → ℤ-is-set _ _))

  ⊞-unit : FormalSum dec
  ⊞-unit = q[ nil ]

  coef-⊞-unit : ∀ a → coef ⊞-unit a == 0
  coef-⊞-unit a = idp

{-
  -- Favonia: These commented-out proofs are valid, but I want to promote
  -- the usage of [coef-ext].

  ⊞-unit-l : ∀ fs → ⊞-unit ⊞ fs == fs
  ⊞-unit-l = SetQuot-elim
    (λ _ → =-preserves-set SetQuotient-is-set)
    (λ l → idp)
    (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _))

  ⊞-unit-r : ∀ fs → fs ⊞ ⊞-unit == fs
  ⊞-unit-r = SetQuot-elim
    (λ _ → =-preserves-set SetQuotient-is-set)
    (λ l → ap q[_] $ ++-nil-r l)
    (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _))
-}

  ⊞-unit-l : ∀ fs → ⊞-unit ⊞ fs == fs
  ⊞-unit-l fs = coef-ext λ a → coef-⊞ ⊞-unit fs a

  ⊞-unit-r : ∀ fs → fs ⊞ ⊞-unit == fs
  ⊞-unit-r fs = coef-ext λ a → coef-⊞ fs ⊞-unit a ∙ ℤ+-unit-r _

  ⊞-assoc : ∀ fs₁ fs₂ fs₃ → (fs₁ ⊞ fs₂) ⊞ fs₃ == fs₁ ⊞ (fs₂ ⊞ fs₃)
  ⊞-assoc fs₁ fs₂ fs₃ = coef-ext λ a →
    coef ((fs₁ ⊞ fs₂) ⊞ fs₃) a
      =⟨ coef-⊞ (fs₁ ⊞ fs₂) fs₃ a ⟩
    coef (fs₁ ⊞ fs₂) a ℤ+ coef fs₃ a
      =⟨ coef-⊞ fs₁ fs₂ a |in-ctx _ℤ+ coef fs₃ a ⟩
    (coef fs₁ a ℤ+ coef fs₂ a) ℤ+ coef fs₃ a
      =⟨ ℤ+-assoc (coef fs₁ a) (coef fs₂ a) (coef fs₃ a) ⟩
    coef fs₁ a ℤ+ (coef fs₂ a ℤ+ coef fs₃ a)
      =⟨ ! $ coef-⊞ fs₂ fs₃ a |in-ctx coef fs₁ a ℤ+_ ⟩
    coef fs₁ a ℤ+ coef (fs₂ ⊞ fs₃) a
      =⟨ ! $ coef-⊞ fs₁ (fs₂ ⊞ fs₃) a ⟩
    coef (fs₁ ⊞ (fs₂ ⊞ fs₃)) a
      =∎

  ⊟-inv-r : ∀ fs → fs ⊞ (⊟ fs) == ⊞-unit
  ⊟-inv-r fs = coef-ext λ a → coef-⊞ fs (⊟ fs) a
                            ∙ ap (coef fs a ℤ+_) (coef-⊟ fs a)
                            ∙ ℤ~-inv-r (coef fs a)

  ⊟-inv-l : ∀ fs → (⊟ fs) ⊞ fs == ⊞-unit
  ⊟-inv-l fs = coef-ext λ a → coef-⊞ (⊟ fs) fs a
                            ∙ ap (_ℤ+ coef fs a) (coef-⊟ fs a)
                            ∙ ℤ~-inv-l (coef fs a)

  FormalSum-group-structure : GroupStructure (FormalSum dec)
  FormalSum-group-structure = record
    { ident = ⊞-unit
    ; inv = ⊟
    ; comp = _⊞_
    ; unit-l = ⊞-unit-l
    ; unit-r = ⊞-unit-r
    ; assoc = ⊞-assoc
    ; inv-r = ⊟-inv-r
    ; inv-l = ⊟-inv-l
    }

  FreeAbelianGroup : Group i
  FreeAbelianGroup = group _ SetQuotient-is-set FormalSum-group-structure

  has-finite-supports : (A → ℤ) → Type i
  has-finite-supports f = Σ (FormalSum dec) λ fs → ∀ a → f a == coef fs a

  has-finite-supports-is-prop : ∀ f → is-prop (has-finite-supports f)
  has-finite-supports-is-prop f = all-paths-is-prop
    λ{(fs₁ , match₁) (fs₂ , match₂) → pair=
      (coef-ext λ a → ! (match₁ a) ∙ match₂ a)
      (prop-has-all-paths-↓ $ Π-is-prop λ _ → ℤ-is-set _ _)}

  module _ {j} (G : Group j) (G-is-abelian : is-abelian G) where

    private
      module G = Group G

    private -- not sure where to put this
      exp : G.El → ℤ → G.El
      exp g (pos 0) = G.ident
      exp g (pos 1) = g
      exp g (pos (S (S n))) = G.comp g (exp g (pos (S n)))
      exp g (negsucc 0) = G.inv g
      exp g (negsucc (S n)) = G.comp (G.inv g) (exp g (negsucc n))

      abstract
        exp-succ : ∀ g z → exp g (succ z) == G.comp g (exp g z)
        exp-succ g (pos 0) = ! $ G.unit-r g
        exp-succ g (pos (S n)) = idp
        exp-succ g (negsucc 0) = ! $ G.inv-r g
        exp-succ g (negsucc (S n)) =
            ! (G.unit-l _)
          ∙ ap (λ g' → G.comp g' (exp g (negsucc n))) (! $ G.inv-r g)
          ∙ G.assoc g (G.inv g) (exp g (negsucc n))

        exp-pred : ∀ g z → exp g (pred z) == G.comp (G.inv g) (exp g z)
        exp-pred g (pos 0) = ! $ G.unit-r (G.inv g)
        exp-pred g (pos 1) = ! $ G.inv-l g
        exp-pred g (pos (S (S n))) =
            ! (G.unit-l _)
          ∙ ap (λ g' → G.comp g' (exp g (pos (S n)))) (! $ G.inv-l g)
          ∙ G.assoc (G.inv g) g (exp g (pos (S n)))
        exp-pred g (negsucc n) = idp

        exp-+ : ∀ g z₁ z₂ → exp g (z₁ ℤ+ z₂) == G.comp (exp g z₁) (exp g z₂)
        exp-+ g (pos 0) z₂ = ! $ G.unit-l _
        exp-+ g (pos 1) z₂ = exp-succ g z₂
        exp-+ g (pos (S (S n))) z₂ =
            exp-succ g (pos (S n) ℤ+ z₂)
          ∙ ap (G.comp g) (exp-+ g (pos (S n)) z₂)
          ∙ ! (G.assoc g (exp g (pos (S n))) (exp g z₂))
        exp-+ g (negsucc 0) z₂ = exp-pred g z₂
        exp-+ g (negsucc (S n)) z₂ =
            exp-pred g (negsucc n ℤ+ z₂)
          ∙ ap (G.comp (G.inv g)) (exp-+ g (negsucc n) z₂)
          ∙ ! (G.assoc (G.inv g) (exp g (negsucc n)) (exp g z₂))

        exp-~ : ∀ g z → exp g (ℤ~ z) == G.inv (exp g z)
        exp-~ g z = ! $ G.inv-unique-l _ _ $ ! (exp-+ g (ℤ~ z) z) ∙ ap (exp g) (ℤ~-inv-l z)

      sum-of-exp : (A → G.El) → (PreFormalSum A → G.El)
      sum-of-exp f = foldr G.comp G.ident ∘ map λ{(z , a) → exp (f a) z}

      abstract
        sum-of-exp-of-same : ∀ f a {l}
          → All (λ za → snd za == a) l
          → sum-of-exp f l == exp (f a) (coef-pre dec l a)
        sum-of-exp-of-same f a₀ {l = .nil} nil = idp
        sum-of-exp-of-same f a₀ {l = (z , a) :: l} (p :: ps) with dec a a₀
        ... | inl _ = ap (λ a → G.comp (exp (f a) z) (sum-of-exp f l)) p
                    ∙ ap (G.comp (exp (f a₀) z)) (sum-of-exp-of-same f a₀ ps)
                    ∙ ! (exp-+ (f a₀) z (coef-pre dec l a₀))
        ... | inr p⊥ = ⊥-rec (p⊥ p)

        sum-of-exp-++ : ∀ f l₁ l₂
          → sum-of-exp f (l₁ ++ l₂) == G.comp (sum-of-exp f l₁) (sum-of-exp f l₂)
        sum-of-exp-++ f nil l₂ = ! $ G.unit-l _
        sum-of-exp-++ f ((z , a) :: l₁) l₂ =
            ap (G.comp (exp (f a) z)) (sum-of-exp-++ f l₁ l₂)
          ∙ ! (G.assoc (exp (f a) z) (sum-of-exp f l₁) (sum-of-exp f l₂))

        sum-of-exp-flip : ∀ f l
          → sum-of-exp f (flip-pre l) == G.inv (sum-of-exp f l)
        sum-of-exp-flip f nil = ! $ G.inv-ident
        sum-of-exp-flip f ((z , a) :: l) =
            ap2 G.comp (exp-~ (f a) z) (sum-of-exp-flip f l)
          ∙ ! (G.inv-comp (sum-of-exp f l) (exp (f a) z))
          ∙ ap G.inv (G-is-abelian (sum-of-exp f l) (exp (f a) z))

      -- XXX Maybe there is another way to prove this.
      record CollectSplitIH (f : A → G.El) (a : A) {n : ℕ} (vec : Vector (ℤ × A) n) : Type (lmax i j) where
        field
          left : List (ℤ × A)
          left-same-base : All (λ za → snd za == a) left
          left-captures-all : coef-pre dec left a == coef-pre dec (fst vec) a
          right : List (ℤ × A)
          right-shorter : length right ≤ n
          pres-sum-of-exp : G.comp (sum-of-exp f left) (sum-of-exp f right)
                         == sum-of-exp f (fst vec)
          pres-coef : ∀ a → coef-pre dec left a ℤ+ coef-pre dec right a == coef-pre dec (fst vec) a

      abstract
        collect-split : ∀ f a {n} (v : Vector (ℤ × A) n) → CollectSplitIH f a v
        collect-split f a₀ (nil , idp) = record {
          left = nil;
          left-same-base = nil;
          left-captures-all = idp;
          right = nil;
          right-shorter = inl idp;
          pres-sum-of-exp = G.unit-l _;
          pres-coef = λ _ → idp}
        collect-split f a₀ ((z , a) :: l , idp) with dec a a₀
        ... | inl p = record {
          left = (z , a) :: left;
          left-same-base = p :: left-same-base;
          left-captures-all = coef-pre-++ dec l[ z , a ] left a₀
            ∙ ap (coef-pre dec l[ z , a ] a₀ ℤ+_) left-captures-all
            ∙ ! (coef-pre-++ dec l[ z , a ] l a₀);
          right = right;
          right-shorter = ≤-trans right-shorter (inr ltS);
          pres-sum-of-exp = G.assoc (exp (f a) z) (sum-of-exp f left) (sum-of-exp f right)
                          ∙ ap (G.comp (exp (f a) z)) pres-sum-of-exp;
          pres-coef = λ a'
            → ap (_ℤ+ coef-pre dec right a') (coef-pre-++ dec l[ z , a ] left a')
            ∙ ℤ+-assoc (coef-pre dec l[ z , a ] a') (coef-pre dec left a') (coef-pre dec right a')
            ∙ ap (coef-pre dec l[ z , a ] a' ℤ+_) (pres-coef a')
            ∙ ! (coef-pre-++ dec l[ z , a ] l a')}
          where open CollectSplitIH (collect-split f a₀ (l , idp))
        ... | inr p⊥ = record {
          left = left;
          left-same-base = left-same-base;
          left-captures-all = left-captures-all';
          right = (z , a) :: right;
          right-shorter = ≤-ap-S right-shorter;
          pres-sum-of-exp = ! (G.assoc (sum-of-exp f left) (exp (f a) z) (sum-of-exp f right))
            ∙ ap (λ g → G.comp g (sum-of-exp f right)) (G-is-abelian (sum-of-exp f left) (exp (f a) z))
            ∙ G.assoc (exp (f a) z) (sum-of-exp f left) (sum-of-exp f right)
            ∙ ap (G.comp (exp (f a) z)) pres-sum-of-exp;
          pres-coef = λ a'
            → ap (coef-pre dec left a' ℤ+_) (coef-pre-++ dec l[ z , a ] right a')
            ∙ ! (ℤ+-assoc (coef-pre dec left a') (coef-pre dec l[ z , a ] a') (coef-pre dec right a'))
            ∙ ap (_ℤ+ coef-pre dec right a') (ℤ+-comm (coef-pre dec left a') (coef-pre dec l[ z , a ] a'))
            ∙ ℤ+-assoc (coef-pre dec l[ z , a ] a') (coef-pre dec left a') (coef-pre dec right a')
            ∙ ap (coef-pre dec l[ z , a ] a' ℤ+_) (pres-coef a')
            ∙ ! (coef-pre-++ dec l[ z , a ] l a')}
          where
            open CollectSplitIH (collect-split f a₀ (l , idp))
            left-captures-all' : coef-pre dec left a₀ == coef-pre dec ((z , a) :: l) a₀
            left-captures-all' with dec a a₀
            ... | inr _ = left-captures-all
            ... | inl p = ⊥-rec (p⊥ p)

        coef-others : ∀ {a b} (p⊥ : a ≠ b) {l}
          → All (λ za → snd za == a) l
          → coef-pre dec l b == 0
        coef-others p⊥ nil = idp
        coef-others {b = b} p⊥ {l = (_ , x) :: l} (p :: ps) with dec x b
        ... | inl q = ⊥-rec (p⊥ (! p ∙ q))
        ... | inr _ = coef-others p⊥ ps

        zero-coef-gives-ident' : ∀ f {m n} (n≤m : n ≤ m) (vec : Vector (ℤ × A) n)
          → (∀ a → coef-pre dec (fst vec) a == 0)
          → sum-of-exp f (fst vec) == G.ident
        zero-coef-gives-ident' f (inr ltS) vec zero-coef
          = zero-coef-gives-ident' f (inl idp) vec zero-coef
        zero-coef-gives-ident' f (inr (ltSR lt)) vec zero-coef
          = zero-coef-gives-ident' f (inr lt) vec zero-coef
        zero-coef-gives-ident' f {m = O} (inl idp) (nil , _) _ = idp
        zero-coef-gives-ident' f {m = O} (inl idp) (_ :: _ , len) _ = ⊥-rec $ ℕ-S≠O _ len
        zero-coef-gives-ident' f {m = S m} (inl idp) (nil , len) _ = ⊥-rec $ ℕ-S≠O _ (! len)
        zero-coef-gives-ident' f {m = S m} (inl idp) ((z , a) :: l , len) zero-coef
          = ap (G.comp (exp (f a) z))
              ( ! pres-sum-of-exp
              ∙ ap2 G.comp
                  (sum-of-exp-of-same f a left-same-base)
                  (zero-coef-gives-ident' f {m = m} right-shorter (right , idp) coef-lemma)
              ∙ G.unit-r _)
          ∙ ! (exp-+ (f a) z (coef-pre dec left a))
          ∙ ap (exp (f a)) ( ap (z ℤ+_) left-captures-all
                           ∙ ! (coef-pre-matching dec z idp l)
                           ∙ zero-coef a)
          where
            open CollectSplitIH (collect-split f a (l , ℕ-S-inj _ _ len))
            coef-lemma : ∀ a' → coef-pre dec right a' == 0
            coef-lemma a' with dec a a'
            ... | inl p rewrite (! p) = ℤ+-cancel-l (coef-pre dec left a) $
              pres-coef a ∙ ! left-captures-all ∙ ! (ℤ+-unit-r _)
            ... | inr p⊥ = ap (_ℤ+ coef-pre dec right a') (! $ coef-others p⊥ left-same-base)
                         ∙ pres-coef a'
                         ∙ ap (_ℤ+ coef-pre dec l a') (! $ coef-others p⊥ (idp :: nil))
                         ∙ ! (coef-pre-++ dec l[ z , a ] l a')
                         ∙ zero-coef a'

        zero-coef-gives-ident : ∀ f l
          → (∀ a → coef-pre dec l a == 0)
          → sum-of-exp f l == G.ident
        zero-coef-gives-ident f l = zero-coef-gives-ident' f (inl idp) (l , idp)

        sum-of-exp-respects-coef : ∀ f l₁ l₂
          → (∀ a → coef-pre dec l₁ a == coef-pre dec l₂ a)
          → sum-of-exp f l₁ == sum-of-exp f l₂
        sum-of-exp-respects-coef f l₁ l₂ coef-match =
            ! (G.inv-inv (sum-of-exp f l₁))
          ∙ G.inv-unique-r _ _ -- G.inv (sum-of-exp f l₁) ⊙ (sum-of-exp f l₂) == G.ident
              ( ap (λ g → G.comp g (sum-of-exp f l₂)) (! $ sum-of-exp-flip f l₁)
              ∙ ! (sum-of-exp-++ f (flip-pre l₁) l₂)
              ∙ zero-coef-gives-ident f (flip-pre l₁ ++ l₂)
                  ( λ a → coef-pre-++ dec (flip-pre l₁) l₂ a
                  ∙ ap (_ℤ+ coef-pre dec l₂ a) (coef-pre-flip dec l₁ a ∙ ap ℤ~ (coef-match a))
                  ∙ ℤ~-inv-l (coef-pre dec l₂ a)))

    FreeAbelianGroup-lift : (A → G.El) → (FreeAbelianGroup →ᴳ G)
    FreeAbelianGroup-lift f = record {
      f = SetQuot-rec G.El-level (sum-of-exp f)
            (λ {l₁} {l₂} rel → sum-of-exp-respects-coef f l₁ l₂ rel);
      pres-comp =
        SetQuot-elim (λ _ → Π-is-set λ _ → =-preserves-set G.El-level)
          (λ fs₁ → SetQuot-elim
            (λ _ → =-preserves-set G.El-level)
            (λ fs₂ → sum-of-exp-++ f fs₁ fs₂)
            (λ _ → prop-has-all-paths-↓ (G.El-level _ _)))
          (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → G.El-level _ _))}

    private
      abstract
        coef-zero : ∀ a
          → (q[ l[ 0 , a ] ] :> FormalSum dec) == q[ nil ]
        coef-zero a = quot-rel lemma where
          lemma : ∀ a' → coef q[ l[ 0 , a ] ] a' == 0
          lemma a' with dec a a'
          lemma a' | inl _ = idp
          lemma a' | inr _ = idp

        coef-split : ∀ z₁ z₂ a
          → (q[ l[ z₁ ℤ+ z₂ , a ] ] :> FormalSum dec)
          == q[ (z₁ , a) :: (z₂ , a) :: nil ]
        coef-split z₁ z₂ a = quot-rel lemma where
          lemma : ∀ a' → coef q[ l[ z₁ ℤ+ z₂ , a ] ] a'
                      == coef q[ (z₁ , a) :: (z₂ , a) :: nil ] a'
          lemma a' with dec a a'
          lemma a' | inl p₁ with dec a a'
          lemma a' | inl p₁ | inl p₂ = ℤ+-assoc z₁ z₂ 0
          lemma a' | inl p₁ | inr p₂⊥ = ⊥-rec (p₂⊥ p₁)
          lemma a' | inr p₁⊥ with dec a a'
          lemma a' | inr p₁⊥ | inl p₂ = ⊥-rec (p₁⊥ p₂)
          lemma a' | inr p₁⊥ | inr p₂⊥ = idp

      module _ (hom : FreeAbelianGroup →ᴳ G) where
        open GroupHom hom
        exp-hom : ∀ z a → exp (f q[ l[ 1 , a ] ]) z == f q[ l[ z , a ] ]
        exp-hom (pos 0) a = ! pres-ident ∙ ap f (! $ coef-zero a)
        exp-hom (pos (S O)) a = idp
        exp-hom (pos (S (S n))) a =
            ap (G.comp (f q[ l[ 1 , a ] ])) (exp-hom (pos (S n)) a)
          ∙ ! (pres-comp q[ l[ 1 , a ] ]  q[ l[ pos (S n) , a ] ])
          ∙ ap f (! $ coef-split 1 (pos (S n)) a)
        exp-hom (negsucc O) a = ! $ pres-inv _
        exp-hom (negsucc (S n)) a =
            ap2 G.comp (! $ pres-inv q[ l[ 1 , a ] ]) (exp-hom (negsucc n) a)
          ∙ ! (pres-comp q[ l[ -1 , a ] ]  q[ l[ negsucc n , a ] ])
          ∙ ap f (! $ coef-split -1 (negsucc n) a)

        sum-of-exp-hom : ∀ l → sum-of-exp (λ a → f q[ l[ 1 , a ] ]) l == f q[ l ]
        sum-of-exp-hom nil = ! pres-ident
        sum-of-exp-hom ((z , a) :: l) =
            ap2 G.comp (exp-hom z a) (sum-of-exp-hom l)
          ∙ ! (pres-comp q[ l[ z , a ] ] q[ l ])

    FreeAbelianGroup-lift-is-equiv : is-equiv FreeAbelianGroup-lift
    FreeAbelianGroup-lift-is-equiv = is-eq _ from to-from from-to where
      to = FreeAbelianGroup-lift

      from : (FreeAbelianGroup →ᴳ G) → (A → G.El)
      from hom a = GroupHom.f hom q[ l[ 1 , a ] ]

      to-from : ∀ h → to (from h) == h
      to-from h = group-hom= $ λ= $ SetQuot-elim
        (λ _ → =-preserves-set G.El-level)
        (λ l → sum-of-exp-hom h l)
        (λ _ → prop-has-all-paths-↓ (G.El-level _ _))

      from-to : ∀ f → from (to f) == f
      from-to f = λ= λ a → G.unit-r (f a)
