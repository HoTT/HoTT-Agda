{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.TwoGroupoid

module lib.groupoids.FundamentalPreTwoGroupoid {i} (A : Type i) where

  ∙-triangle-identity : {x y z : A} (a : x == y) (b : y == z)
    → ap (λ s → s ∙ b) (∙-unit-r a) == ∙-assoc a idp b ∙ ap (_∙_ a) idp
  ∙-triangle-identity idp b = idp

  ∙-pentagon-identity : {v w x y z : A} (a : v == w) (b : w == x) (c : x == y) (d : y == z)
    → ∙-assoc (a ∙ b) c d ∙ ∙-assoc a b (c ∙ d)
      == ap (λ s → s ∙ d) (∙-assoc a b c) ∙ ∙-assoc a (b ∙ c) d ∙ ap (_∙_ a) (∙-assoc b c d)
  ∙-pentagon-identity idp idp c d = idp

  ∙-inv-coherence : {x y : A} (a : x == y)
    → ap (λ s → s ∙ a) (!-inv-r a) ∙ idp
    == ∙-assoc a (! a) a ∙ ap (_∙_ a) (!-inv-l a) ∙ ∙-unit-r a
  ∙-inv-coherence idp = idp

  fundamental-two-one-semi-category-of-a-two-type : {{_ : has-level 2 A}} → TwoOneSemiCategory i i
  fundamental-two-one-semi-category-of-a-two-type =
    record
    { El = A
    ; Arr = _==_
    ; Arr-level = λ _ _ → ⟨⟩
    ; two-one-semi-cat-struct = record
      { comp = _∙_
      ; assoc = λ a b c → ∙-assoc a b c
      ; pentagon-identity = ∙-pentagon-identity
      }
    }

  fundamental-pretwogroupoid-of-a-two-type : {{_ : has-level 2 A}} → PreTwoGroupoid i i
  fundamental-pretwogroupoid-of-a-two-type =
    record
    { two-one-semi-cat = fundamental-two-one-semi-category-of-a-two-type
    ; two-groupoid-struct = record
      { ident = idp
      ; inv = λ a → ! a
      ; unit-l = λ _ → idp
      ; unit-r = λ a → ∙-unit-r a
      ; inv-l = λ a → !-inv-l a
      ; inv-r = λ a → !-inv-r a
      ; triangle-identity = ∙-triangle-identity
      ; inv-coherence = ∙-inv-coherence
      }
    }

  _=₁_ : A → A → Type i
  _=₁_ x y = Trunc 1 (x == y)

  !₁ : {x y : A} → x =₁ y → y =₁ x
  !₁ = Trunc-fmap !

  infixr 80 _∙₁_
  _∙₁_ : {x y z : A} → x =₁ y → y =₁ z → x =₁ z
  _∙₁_ = Trunc-fmap2 _∙_

  idp₁ : {x : A} → x =₁ x
  idp₁ = [ idp ]

  ∙₁-unit-l : {x y : A} (a : x =₁ y) → idp₁ ∙₁ a == a
  ∙₁-unit-l = Trunc-elim (λ _ → idp)

  ∙₁-unit-r : {x y : A} (a : x =₁ y) → a ∙₁ idp₁ == a
  ∙₁-unit-r = Trunc-elim (λ a → ap [_]₁ (∙-unit-r a))

  ∙₁-assoc : {x y z w : A} (a : x =₁ y) (b : y =₁ z) (c : z =₁ w)
    → (a ∙₁ b) ∙₁ c == a ∙₁ (b ∙₁ c)
  ∙₁-assoc {x} {y} {z} {w} a b c =
    Trunc-elim {P = λ a → P a b c}
      (λ a → Trunc-elim {P = λ b → P [ a ] b c}
        (λ b → Trunc-elim {P = λ c → P [ a ] [ b ] c}
          (λ c → ap [_]₁ (∙-assoc a b c))
          c)
        b)
      a
    where
    P : x =₁ y → y =₁ z → z =₁ w → Type i
    P a b c = (a ∙₁ b) ∙₁ c == a ∙₁ (b ∙₁ c)

  !₁-inv-l : {x y : A} → (a : x =₁ y) → !₁ a ∙₁ a == idp₁
  !₁-inv-l = Trunc-elim (λ p → ap [_]₁ (!-inv-l p))

  !₁-inv-r : {x y : A} → (a : x =₁ y) → a ∙₁ !₁ a == idp₁
  !₁-inv-r = Trunc-elim (λ p → ap [_]₁ (!-inv-r p))

  ∙₁-triangle-identity : {x y z : A} (a : x =₁ y) (b : y =₁ z)
    → ap (λ s → s ∙₁ b) (∙₁-unit-r a) ==
      ∙₁-assoc a idp₁ b ∙ ap (_∙₁_ a) (∙₁-unit-l b)
  ∙₁-triangle-identity {x} {y} {z} a b =
    Trunc-elim {P = λ a → P a b}
      (λ p → Trunc-elim {P = λ b → P [ p ] b}
        (λ q → ∙₁-triangle-identity' p q)
        b)
      a
    where
    P : {u v w : A} → u =₁ v → v =₁ w → Type i
    P a b = ap (λ s → s ∙₁ b) (∙₁-unit-r a)
            == ∙₁-assoc a idp₁ b ∙ ap (_∙₁_ a) (∙₁-unit-l b)
    ∙₁-triangle-identity' : {u v w : A} (p : u == v) (q : v == w) → P [ p ] [ q ]
    ∙₁-triangle-identity' idp q = idp

  ∙₁-pentagon-identity : {v w x y z : A}
    (a : v =₁ w) (b : w =₁ x) (c : x =₁ y) (d : y =₁ z)
    → ∙₁-assoc (a ∙₁ b) c d ∙ ∙₁-assoc a b (c ∙₁ d)
      == ap (λ s → s ∙₁ d) (∙₁-assoc a b c) ∙
            ∙₁-assoc a (b ∙₁ c) d ∙ ap (_∙₁_ a) (∙₁-assoc b c d)
  ∙₁-pentagon-identity a b c d =
    Trunc-elim {P = λ a → P a b c d}
      (λ a' → Trunc-elim {P = λ b → P [ a' ] b c d}
        (λ b' → Trunc-elim {P = λ c → P [ a' ] [ b' ] c d}
          (λ c' → Trunc-elim {P = λ d → P [ a' ] [ b' ] [ c' ] d}
            (λ d' → ∙₁-pentagon-identity' a' b' c' d')
            d)
          c)
        b)
      a
    where
    P : {k l m n o : A} → k =₁ l → l =₁ m → m =₁ n → n =₁ o → Type i
    P a b c d = ∙₁-assoc (a ∙₁ b) c d ∙ ∙₁-assoc a b (c ∙₁ d)
                == ap (λ s → s ∙₁ d) (∙₁-assoc a b c) ∙
                     ∙₁-assoc a (b ∙₁ c) d ∙ ap (_∙₁_ a) (∙₁-assoc b c d)
    ∙₁-pentagon-identity' : {k l m n o : A}
      (a' : k == l) (b' : l == m) (c' : m == n) (d' : n == o)
      → P [ a' ] [ b' ] [ c' ] [ d' ]
    ∙₁-pentagon-identity' idp idp c' d' = idp

  ∙₁-inv-coherence : {x y : A} (a : x =₁ y)
    → ap (λ s → s ∙₁ a) (!₁-inv-r a) ∙ ∙₁-unit-l a
      == ∙₁-assoc a (!₁ a) a ∙ ap (_∙₁_ a) (!₁-inv-l a) ∙ ∙₁-unit-r a
  ∙₁-inv-coherence = Trunc-elim ∙₁-inv-coherence'
    where
    P : {v w : A} → v =₁ w → Type i
    P a =
      ap (λ s → s ∙₁ a) (!₁-inv-r a) ∙ ∙₁-unit-l a
      == ∙₁-assoc a (!₁ a) a ∙ ap (_∙₁_ a) (!₁-inv-l a) ∙ ∙₁-unit-r a
    ∙₁-inv-coherence' : {v w : A} (p : v == w) → P [ p ]₁
    ∙₁-inv-coherence' idp = idp

  fundamental-two-one-semi-category : TwoOneSemiCategory i i
  fundamental-two-one-semi-category =
    record
    { El = A
    ; Arr = _=₁_
    ; Arr-level = λ _ _ → Trunc-level
    ; two-one-semi-cat-struct = record
      { comp = _∙₁_
      ; assoc = ∙₁-assoc
      ; pentagon-identity = ∙₁-pentagon-identity
      }
    }

  fundamental-pretwogroupoid : PreTwoGroupoid i i
  fundamental-pretwogroupoid =
    record
    { two-one-semi-cat = fundamental-two-one-semi-category
    ; two-groupoid-struct = record
      { ident = idp₁
      ; inv = !₁
      ; unit-l = ∙₁-unit-l
      ; unit-r = ∙₁-unit-r
      ; inv-l = !₁-inv-l
      ; inv-r = !₁-inv-r
      ; triangle-identity = ∙₁-triangle-identity
      ; inv-coherence = ∙₁-inv-coherence
      }
    }
