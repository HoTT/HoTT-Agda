{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

module lib.PathFunctor where

{- Nondependent stuff -}
module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  !-ap : {x y : A} (p : x == y)
    → ! (ap f p) == ap f (! p)
  !-ap idp = idp

  ap-! : {x y : A} (p : x == y)
    → ap f (! p) == ! (ap f p)
  ap-! idp = idp

  ∙-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙ ap f q == ap f (p ∙ q)
  ∙-ap idp q = idp

  ap-∙ : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙ q) == ap f p ∙ ap f q
  ap-∙ idp q = idp

  !ap-∙=∙-ap : {x y z : A} (p : x == y) (q : y == z)
    → ! (ap-∙ p q) == ∙-ap p q
  !ap-∙=∙-ap idp q = idp

  ∙∙-ap : {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
    → ap f p ∙ ap f q ∙ ap f r == ap f (p ∙ q ∙ r)
  ∙∙-ap idp idp r = idp

  ap-∙∙ : {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
    → ap f (p ∙ q ∙ r) == ap f p ∙ ap f q ∙ ap f r
  ap-∙∙ idp idp r = idp

  ap-∙∙∙ : {x y z w t : A} (p : x == y) (q : y == z) (r : z == w) (s : w == t)
    → ap f (p ∙ q ∙ r ∙ s) == ap f p ∙ ap f q ∙ ap f r ∙ ap f s
  ap-∙∙∙ idp idp idp s = idp

  ∙'-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙' ap f q == ap f (p ∙' q)
  ∙'-ap p idp = idp

  -- note: ap-∙' is defined in PathGroupoid

{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} (f : Π A B) where

  apd-∙ : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙ q) == apd f p ∙ᵈ apd f q
  apd-∙ idp idp = idp

  apd-∙' : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙' q) == apd f p ∙'ᵈ apd f q
  apd-∙' idp idp = idp

  apd-! : {x y : A} (p : x == y)
    → apd f (! p) == !ᵈ (apd f p)
  apd-! idp = idp

{- Over stuff -}
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : {a : A} → B a → C a) where

  ap↓-◃ : {x y z : A} {u : B x} {v : B y} {w : B z}
    {p : x == y} {p' : y == z} (q : u == v [ B ↓ p ]) (r : v == w [ B ↓ p' ])
    → ap↓ f (q ◃ r) == ap↓ f q ◃ ap↓ f r
  ap↓-◃ {p = idp} {p' = idp} idp idp = idp

  ap↓-▹! : {x y z : A} {u : B x} {v : B y} {w : B z}
    {p : x == y} {p' : z == y} (q : u == v [ B ↓ p ]) (r : w == v [ B ↓ p' ])
    → ap↓ f (q ▹! r) == ap↓ f q ▹! ap↓ f r
  ap↓-▹! {p = idp} {p' = idp} idp idp = idp

{- Fuse and unfuse -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where
  ∘-ap : {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
  ∘-ap idp = idp

  ap-∘ : {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
  ap-∘ idp = idp

  !ap-∘=∘-ap : {x y : A} (p : x == y) → ! (ap-∘ p) == ∘-ap p
  !ap-∘=∘-ap idp = idp

ap-idf : ∀ {i} {A : Type i} {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf idp = idp

{- Functoriality of [coe] -}
coe-∙ : ∀ {i} {A B C : Type i} (p : A == B) (q : B == C) (a : A)
  → coe (p ∙ q) a == coe q (coe p a)
coe-∙ idp q a = idp

coe-! : ∀ {i} {A B : Type i} (p : A == B) (b : B) → coe (! p) b == coe! p b
coe-! idp b = idp

coe!-inv-r : ∀ {i} {A B : Type i} (p : A == B) (b : B)
  → coe p (coe! p b) == b
coe!-inv-r idp b = idp

coe!-inv-l : ∀ {i} {A B : Type i} (p : A == B) (a : A)
  → coe! p (coe p a) == a
coe!-inv-l idp a = idp

coe-inv-adj : ∀ {i} {A B : Type i} (p : A == B) (a : A) →
  ap (coe p) (coe!-inv-l p a) == coe!-inv-r p (coe p a)
coe-inv-adj idp a = idp

coe!-inv-adj : ∀ {i} {A B : Type i} (p : A == B) (b : B) →
  ap (coe! p) (coe!-inv-r p b) == coe!-inv-l p (coe! p b)
coe!-inv-adj idp b = idp

coe-ap-! : ∀ {i j} {A : Type i} (P : A → Type j) {a b : A} (p : a == b)
  (x : P b)
  → coe (ap P (! p)) x == coe! (ap P p) x
coe-ap-! P idp x = idp

{- Functoriality of transport -}
transp-∙ : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
  (p : x == y) (q : y == z) (b : B x)
  → transport B (p ∙ q) b == transport B q (transport B p b)
transp-∙ idp _ _ = idp

transp-∙' : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A}
  (p : x == y) (q : y == z) (b : B x)
  → transport B (p ∙' q) b == transport B q (transport B p b)
transp-∙' _ idp _ = idp

{- Naturality of transport -}
transp-naturality : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (u : {a : A} → B a → C a)
  {a₀ a₁ : A} (p : a₀ == a₁)
  → u ∘ transport B p == transport C p ∘ u
transp-naturality f idp = idp

transp-idp : ∀ {i j} {A : Type i} {B : Type j}
  (f : A → B) {x y : A} (p : x == y)
  → transport (λ a → f a == f a) p idp == idp
transp-idp f idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ap-transp : (f g : A → B) {a₀ a₁ : A} (p : a₀ == a₁) (h : f a₀ == g a₀)
    → h ∙ ap g p == ap f p ∙ transport (λ a → f a == g a) p h
  ap-transp f g p@idp h = ∙-unit-r h

  ap-transp-idp : (f : A → B)
    {a₀ a₁ : A} (p : a₀ == a₁)
    → ap-transp f f p idp ◃∙
      ap (ap f p ∙_) (transp-idp f p) ◃∙
      ∙-unit-r (ap f p) ◃∎
      =ₛ
      []
  ap-transp-idp f p@idp = =ₛ-in idp

{- for functions with two arguments -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap2 : {x y : A} {w z : B}
    → (x == y) → (w == z) → f x w == f y z
  ap2 idp idp = idp

  ap2-out : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 p q ◃∎ =ₛ ap (λ u → f u w) p ◃∙ ap (λ v → f y v) q ◃∎
  ap2-out idp idp = =ₛ-in idp

  ap2-out' : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 p q ◃∎ =ₛ ap (λ u → f x u) q ◃∙ ap (λ v → f v z) p ◃∎
  ap2-out' idp idp = =ₛ-in idp

  ap2-idp-l : {x : A} {w z : B} (q : w == z)
    → ap2 (idp {a = x}) q == ap (f x) q
  ap2-idp-l idp = idp

  ap2-idp-r : {x y : A} {w : B} (p : x == y)
    → ap2 p (idp {a = w}) == ap (λ z → f z w) p
  ap2-idp-r idp = idp

  ap2-! : {a a' : A} {b b' : B} (p : a == a') (q : b == b')
    → ap2 (! p) (! q) == ! (ap2 p q)
  ap2-! idp idp = idp

  !-ap2 : {a a' : A} {b b' : B} (p : a == a') (q : b == b')
    → ! (ap2 p q) == ap2 (! p) (! q)
  !-ap2 idp idp = idp

  ap2-∙ : {a a' a'' : A} {b b' b'' : B}
    (p : a == a') (p' : a' == a'')
    (q : b == b') (q' : b' == b'')
    → ap2 (p ∙ p') (q ∙ q') == ap2 p q ∙ ap2 p' q'
  ap2-∙ idp p' idp q' = idp

  ∙-ap2 : {a a' a'' : A} {b b' b'' : B}
    (p : a == a') (p' : a' == a'')
    (q : b == b') (q' : b' == b'')
    → ap2 p q ∙ ap2 p' q' == ap2 (p ∙ p') (q ∙ q')
  ∙-ap2 idp p' idp q' = idp

{- ap2 lemmas -}
module _ {i j} {A : Type i} {B : Type j} where

  ap2-fst : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 (curry fst) p q == p
  ap2-fst idp idp = idp

  ap2-snd : {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap2 (curry snd) p q == q
  ap2-snd idp idp = idp

  ap-ap2 : ∀ {k l} {C : Type k} {D : Type l}
    (g : C → D) (f : A → B → C) {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap g (ap2 f p q) == ap2 (λ a b → g (f a b)) p q
  ap-ap2 g f idp idp = idp

  ap2-ap-l : ∀ {k l} {C : Type k} {D : Type l}
    (g : B → C → D) (f : A → B) {x y : A} {w z : C}
    (p : x == y) (q : w == z)
    → ap2 g (ap f p) q == ap2 (λ a c → g (f a) c) p q
  ap2-ap-l g f idp idp = idp

  ap2-ap-r : ∀ {k l} {C : Type k} {D : Type l}
    (g : A → C → D) (f : B → C) {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap2 g p (ap f q) == ap2 (λ a b → g a (f b)) p q
  ap2-ap-r g f idp idp = idp

  ap2-ap-lr : ∀ {k l m} {C : Type k} {D : Type l} {E : Type m}
    (g : C → D → E) (f : A → C) (h : B → D)
    {x y : A} {w z : B}
    (p : x == y) (q : w == z)
    → ap2 g (ap f p) (ap h q) == ap2 (λ a b → g (f a) (h b)) p q
  ap2-ap-lr g f h idp idp = idp

  ap2-diag : (f : A → A → B)
    {x y : A} (p : x == y)
    → ap2 f p p == ap (λ x → f x x) p
  ap2-diag f idp = idp

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) where

  module _ {a a' a'' : A} (p : a == a') (p' : a' == a'') where
    ap-∘-∙-coh-seq₁ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₁ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∙ (g ∘ f) p p' ⟫
      ap (g ∘ f) p ∙ ap (g ∘ f) p'
        =⟪ ap2 _∙_ (ap-∘ g f p) (ap-∘ g f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

    ap-∘-∙-coh-seq₂ :
      ap (g ∘ f) (p ∙ p') =-= ap g (ap f p) ∙ ap g (ap f p')
    ap-∘-∙-coh-seq₂ =
      ap (g ∘ f) (p ∙ p')
        =⟪ ap-∘ g f (p ∙ p') ⟫
      ap g (ap f (p ∙ p'))
        =⟪ ap (ap g) (ap-∙ f p p') ⟫
      ap g (ap f p ∙ ap f p')
        =⟪ ap-∙ g (ap f p) (ap f p') ⟫
      ap g (ap f p) ∙ ap g (ap f p') ∎∎

  ap-∘-∙-coh :  {a a' a'' : A} (p : a == a') (p' : a' == a'')
    → ap-∘-∙-coh-seq₁ p p' =ₛ ap-∘-∙-coh-seq₂ p p'
  ap-∘-∙-coh idp idp = =ₛ-in idp

module _ {i j} {A : Type i} {B : Type j} (b : B) where

  ap-cst : {x y : A} (p : x == y)
    → ap (cst b) p == idp
  ap-cst idp = idp

  ap-cst-coh : {x y z : A} (p : x == y) (q : y == z)
    → ap-cst (p ∙ q) ◃∎
      =ₛ
      ap-∙ (cst b) p q ◃∙
      ap2 _∙_ (ap-cst p) (ap-cst q) ◃∎
  ap-cst-coh idp idp = =ₛ-in idp

{- Naturality of homotopies -}

module _ {i} {A : Type i} where
  homotopy-naturality : ∀ {k} {B : Type k} (f g : A → B)
    (h : (x : A) → f x == g x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality f g h {x} idp =
    =ₛ-in (! (∙-unit-r (h x)))

  homotopy-naturality-to-idf : (f : A → A)
    (h : (x : A) → f x == x) {x y : A} (p : x == y)
    → ap f p ◃∙ h y ◃∎ =ₛ h x ◃∙ p ◃∎
  homotopy-naturality-to-idf f h {x} p = =ₛ-in $
    =ₛ-out (homotopy-naturality f (λ a → a) h p) ∙ ap (λ w → h x ∙ w) (ap-idf p)

  homotopy-naturality-from-idf : (g : A → A)
    (h : (x : A) → x == g x) {x y : A} (p : x == y)
    → p ◃∙ h y ◃∎ =ₛ h x ◃∙ ap g p ◃∎
  homotopy-naturality-from-idf g h {y = y} p = =ₛ-in $
    ap (λ w → w ∙ h y) (! (ap-idf p)) ∙ =ₛ-out (homotopy-naturality (λ a → a) g h p)

  homotopy-naturality-to-cst : ∀ {k} {B : Type k} (f : A → B) (b : B)
    (h : (x : A) → f x == b) {x y : A} (p : x == y)
    → ap f p == h x ∙ ! (h y)
  homotopy-naturality-to-cst f b h {x} p@idp = ! (!-inv-r (h x))

  homotopy-naturality-cst-to-cst : ∀ {k} {B : Type k}
    (b : B) {x y : A} (p : x == y)
    → homotopy-naturality-to-cst (cst b) b (λ a → idp) p ==
      ap-cst b p
  homotopy-naturality-cst-to-cst b p@idp = idp

  homotopy-naturality-cst-to-cst' : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y : A} (p : x == y)
    → homotopy-naturality-to-cst (cst b₀) b₁ h p ◃∙
      ap (λ v → h v ∙ ! (h y)) p ◃∙
      !-inv-r (h y) ◃∎
      =ₛ
      ap-cst b₀ p ◃∎
  homotopy-naturality-cst-to-cst' b₀ b₁ h {x} p@idp =
    =ₛ-in (!-inv-l (!-inv-r (h x)))

  homotopy-naturality-cst-to-cst-comp : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y z : A} (p : x == y) (q : y == z)
    → homotopy-naturality-to-cst (cst b₀) b₁ h (p ∙ q) ◃∙
      ap (λ v → h v ∙ ! (h z)) p ◃∎
      =ₛ
      ap-∙ (cst b₀) p q ◃∙
      ap (_∙ ap (cst b₀) q) (ap-cst b₀ p) ◃∙
      homotopy-naturality-to-cst (cst b₀) b₁ h q ◃∎
  homotopy-naturality-cst-to-cst-comp b₀ b₁ h {x} p@idp q@idp =
    =ₛ-in (∙-unit-r (! (!-inv-r (h x))))

  homotopy-naturality-cst-to-cst-comp' : ∀ {k} {B : Type k}
    (b₀ b₁ : B) (h : A → b₀ == b₁) {x y z : A} (p : x == z) (q : x == y)
    → homotopy-naturality-to-cst (cst b₀) b₁ h p ◃∙
      ap (λ v → h v ∙ ! (h z)) q ◃∎
      =ₛ
      ap-cst b₀ p ◃∙
      ! (ap-cst b₀ (! q ∙ p)) ◃∙
      homotopy-naturality-to-cst (cst b₀) b₁ h (! q ∙ p) ◃∎
  homotopy-naturality-cst-to-cst-comp' b₀ b₁ h {x} p@idp q@idp =
    =ₛ-in (∙-unit-r (! (!-inv-r (h x))))

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (f g : A → B → C) (h : ∀ a b → f a b == g a b) where
  homotopy-naturality2 : {a₀ a₁ : A} {b₀ b₁ : B} (p : a₀ == a₁) (q : b₀ == b₁)
    → ap2 f p q ◃∙ h a₁ b₁ ◃∎ =ₛ h a₀ b₀ ◃∙ ap2 g p q ◃∎
  homotopy-naturality2 {a₀ = a} {b₀ = b} idp idp =
    =ₛ-in (! (∙-unit-r (h a b)))

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) where

  ap-comm : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ∙ ap (λ z → f a₁ z) q ==
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm p q = ! (=ₛ-out (ap2-out f p q)) ∙ =ₛ-out (ap2-out' f p q)

  ap-comm-=ₛ : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ◃∙ ap (λ z → f a₁ z) q ◃∎ =ₛ
      ap (λ z → f a₀ z) q ◃∙ ap (λ a → f a b₁) p ◃∎
  ap-comm-=ₛ p q = =ₛ-in (ap-comm p q)

  ap-comm' : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap (λ a → f a b₀) p ∙' ap (λ z → f a₁ z) q ==
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm' p idp = idp

  ap-comm-cst-seq : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    (c : C) (h₀ : ∀ b → f a₀ b == c)
    → ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q =-=
      ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p
  ap-comm-cst-seq {a₀} {a₁} p {b₀} {b₁} q c h₀ =
    ap (λ a → f a b₀) p ∙ ap (λ b → f a₁ b) q
      =⟪ ap (ap (λ a → f a b₀) p ∙_) $
        homotopy-naturality-to-cst (λ b → f a₁ b) c h₁ q ⟫
    ap (λ a → f a b₀) p ∙ h₁ b₀ ∙ ! (h₁ b₁)
      =⟪ ap (ap (λ a → f a b₀) p ∙_) $ ap (λ k → k h₀) $
        transp-naturality {B = λ a → ∀ b → f a b == c} (λ h → h b₀ ∙ ! (h b₁)) p ⟫
    ap (λ a → f a b₀) p ∙ transport (λ a → f a b₀ == f a b₁) p (h₀ b₀ ∙ ! (h₀ b₁))
      =⟪ ! (ap-transp (λ a → f a b₀) (λ a → f a b₁) p (h₀ b₀ ∙ ! (h₀ b₁))) ⟫
    (h₀ b₀ ∙ ! (h₀ b₁)) ∙ ap (λ a → f a b₁) p
      =⟪ ! (ap (_∙ ap (λ a → f a b₁) p) $
              (homotopy-naturality-to-cst (λ b → f a₀ b) c h₀ q)) ⟫
    ap (λ z → f a₀ z) q ∙ ap (λ a → f a b₁) p ∎∎
    where
      h₁ : ∀ b → f a₁ b == c
      h₁ = transport (λ a → ∀ b → f a b == c) p h₀

  ap-comm-cst-coh : {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    (c : C) (h₀ : ∀ b → f a₀ b == c)
    → ap-comm p q ◃∎ =ₛ
      ap-comm-cst-seq p q c h₀
  ap-comm-cst-coh p@idp {b₀} q@idp c h₀ = =ₛ-in $ ! $
    ap (idp ∙_) (! (!-inv-r (h₀ b₀))) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀))))
      =⟨ ap (_∙ ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙ ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀)))))
            (ap-idf (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ! (ap (_∙ idp) (! (!-inv-r (h₀ b₀))))
      =⟨ ap (λ v → ! (!-inv-r (h₀ b₀)) ∙ ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙ v)
            (!-ap (_∙ idp) (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙
    ! (∙-unit-r (h₀ b₀ ∙ ! (h₀ b₀))) ∙
    ap (_∙ idp) (! (! (!-inv-r (h₀ b₀))))
      =⟨ ap (! (!-inv-r (h₀ b₀)) ∙_) $ ! $ =ₛ-out $
         homotopy-naturality-from-idf (_∙ idp)
                                      (λ p → ! (∙-unit-r p))
                                      (! (! (!-inv-r (h₀ b₀)))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙ ! (! (!-inv-r (h₀ b₀))) ∙ idp
      =⟨ ap (! (!-inv-r (h₀ b₀)) ∙_) (∙-unit-r (! (! (!-inv-r (h₀ b₀))))) ⟩
    ! (!-inv-r (h₀ b₀)) ∙ ! (! (!-inv-r (h₀ b₀)))
      =⟨ !-inv-r (! (!-inv-r (h₀ b₀))) ⟩
    idp =∎

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} where

  ap-comm-comm : (f : A → B → C) {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
    → ap-comm f p q == ! (ap-comm (λ x y → f y x) q p)
  ap-comm-comm f p@idp q@idp = idp

module _ {i} {A : Type i} where

  -- unsure where this belongs
  transp-cst=idf : {a x y : A} (p : x == y) (q : a == x)
    → transport (λ x → a == x) p q == q ∙ p
  transp-cst=idf idp q = ! (∙-unit-r q)

  transp-cst=idf-pentagon : {a x y z : A}
    (p : x == y) (q : y == z) (r : a == x)
    → transp-cst=idf (p ∙ q) r ◃∎ =ₛ
      transp-∙ p q r ◃∙
      ap (transport (λ x → a == x) q) (transp-cst=idf p r) ◃∙
      transp-cst=idf q (r ∙ p) ◃∙
      ∙-assoc r p q ◃∎
  transp-cst=idf-pentagon idp q idp =
    =ₛ-in (! (∙-unit-r (transp-cst=idf q idp)))

{- for functions with more arguments -}
module _ {i₀ i₁ i₂ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B : Type j} (f : A₀ → A₁ → A₂ → B) where

  ap3 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → f x₀ x₁ x₂ == f y₀ y₁ y₂
  ap3 idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → B) where

  ap4 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → f x₀ x₁ x₂ x₃ == f y₀ y₁ y₂ y₃
  ap4 idp idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ i₄ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {A₄ : Type i₄} {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → A₄ → B) where

  ap5 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃} {x₄ y₄ : A₄}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → (x₄ == y₄)
    → f x₀ x₁ x₂ x₃ x₄ == f y₀ y₁ y₂ y₃ y₄
  ap5 idp idp idp idp idp = idp

module _ {i₀ i₁ i₂ i₃ i₄ i₅ j} {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂} {A₃ : Type i₃}
  {A₄ : Type i₄} {A₅ : Type i₅} {B : Type j} (f : A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → B) where

  ap6 : {x₀ y₀ : A₀} {x₁ y₁ : A₁} {x₂ y₂ : A₂} {x₃ y₃ : A₃} {x₄ y₄ : A₄} {x₅ y₅ : A₅}
    → (x₀ == y₀) → (x₁ == y₁) → (x₂ == y₂) → (x₃ == y₃) → (x₄ == y₄) → (x₅ == y₅)
    → f x₀ x₁ x₂ x₃ x₄ x₅ == f y₀ y₁ y₂ y₃ y₄ y₅
  ap6 idp idp idp idp idp idp = idp
