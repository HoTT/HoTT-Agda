{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Fin
open import lib.types.Pi
open import lib.types.Truncation

module lib.types.Choice where

unchoose : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j}
  → Trunc n (Π A B) → Π A (Trunc n ∘ B)
unchoose = Trunc-rec (λ f → [_] ∘ f)

has-choice : ∀ {i} (n : ℕ₋₂) (A : Type i) j → Type (lmax i (lsucc j))
has-choice {i} n A j = (B : A → Type j) → is-equiv (unchoose {n = n} {A} {B})

Empty-has-choice : ∀ {n} {j} → has-choice n Empty j
Empty-has-choice {n} B = is-eq to from to-from from-to where
  to = unchoose {n = n} {Empty} {B}

  from : Π Empty (Trunc n ∘ B) → Trunc n (Π Empty B)
  from _ = [ (λ{()}) ]

  abstract
    to-from : ∀ f → to (from f) == f
    to-from _ = λ= λ{()}

    from-to : ∀ f → from (to f) == f
    from-to = Trunc-elim (λ _ → ap [_] (λ= λ{()}))

Unit-has-choice : ∀ {n} {j} → has-choice n Unit j
Unit-has-choice {n} B = is-eq to from to-from from-to where
  to = unchoose {n = n} {Unit} {B}

  Unit-elim' : B unit → Π Unit B
  Unit-elim' u unit = u

  from : Π Unit (Trunc n ∘ B) → Trunc n (Π Unit B)
  from f = Trunc-fmap Unit-elim' (f unit)

  abstract
    to-from : ∀ f → to (from f) == f
    to-from f = λ= λ{unit →
      Trunc-elim
        {P = λ f-unit → to (Trunc-fmap Unit-elim' f-unit) unit == f-unit}
        (λ _ → idp)
        (f unit)}

    from-to : ∀ f → from (to f) == f
    from-to = Trunc-elim (λ f → ap [_] (λ= λ{unit → idp}))

Coprod-has-choice : ∀ {i j} {n} {A : Type i} {B : Type j} {k}
  → has-choice n A k → has-choice n B k
  → has-choice n (A ⊔ B) k
Coprod-has-choice {n = n} {A} {B} A-hc B-hc C = is-eq to from to-from from-to where
  A-unchoose = unchoose {n = n} {A} {C ∘ inl}
  B-unchoose = unchoose {n = n} {B} {C ∘ inr}
  module A-unchoose = is-equiv (A-hc (C ∘ inl))
  module B-unchoose = is-equiv (B-hc (C ∘ inr))

  to = unchoose {n = n} {A ⊔ B} {C}

  from : Π (A ⊔ B) (Trunc n ∘ C) → Trunc n (Π (A ⊔ B) C)
  from f = Trunc-fmap2 Coprod-elim (A-unchoose.g (f ∘ inl)) (B-unchoose.g (f ∘ inr))

  abstract
    to-from-inl' : ∀ f a → to (from f) (inl a) == A-unchoose (A-unchoose.g (f ∘ inl)) a
    to-from-inl' f a = Trunc-elim
      {P = λ f-inl → to (Trunc-fmap2 Coprod-elim f-inl (B-unchoose.g (f ∘ inr))) (inl a) == A-unchoose f-inl a}
      (λ f-inl → Trunc-elim
        {P = λ f-inr → to (Trunc-fmap2 Coprod-elim [ f-inl ] f-inr) (inl a) == [ f-inl a ]}
        (λ f-inr → idp)
        (B-unchoose.g (f ∘ inr)))
      (A-unchoose.g (f ∘ inl))

    to-from-inl : ∀ f a → to (from f) (inl a) == f (inl a)
    to-from-inl f a = to-from-inl' f a ∙ app= (A-unchoose.f-g (f ∘ inl)) a

    to-from-inr' : ∀ f b → to (from f) (inr b) == B-unchoose (B-unchoose.g (f ∘ inr)) b
    to-from-inr' f b = Trunc-elim
      {P = λ f-inr → to (Trunc-fmap2 Coprod-elim (A-unchoose.g (f ∘ inl)) f-inr) (inr b) == B-unchoose f-inr b}
      (λ f-inr → Trunc-elim
        {P = λ f-inl → to (Trunc-fmap2 Coprod-elim f-inl [ f-inr ]) (inr b) == [ f-inr b ]}
        (λ f-inl → idp)
        (A-unchoose.g (f ∘ inl)))
      (B-unchoose.g (f ∘ inr))

    to-from-inr : ∀ f b → to (from f) (inr b) == f (inr b)
    to-from-inr f b = to-from-inr' f b ∙ app= (B-unchoose.f-g (f ∘ inr)) b

    to-from : ∀ f → to (from f) == f
    to-from f = λ= λ{(inl a) → to-from-inl f a; (inr b) → to-from-inr f b}

    from-to : ∀ f → from (to f) == f
    from-to = Trunc-elim
      (λ f →
        Trunc-fmap2 Coprod-elim (A-unchoose.g (λ a → [ f (inl a)])) (B-unchoose.g (λ b → [ f (inr b)]))
          =⟨ ap2 (Trunc-fmap2 Coprod-elim) (A-unchoose.g-f [ f ∘ inl ]) (B-unchoose.g-f [ f ∘ inr ]) ⟩
        [ Coprod-elim (f ∘ inl) (f ∘ inr) ]
          =⟨ ap [_] $ λ= (λ{(inl _) → idp; (inr _) → idp}) ⟩
        [ f ]
          =∎)

equiv-preserves-choice : ∀ {i j} {n} {A : Type i} {B : Type j} (e : A ≃ B) {k}
  → has-choice n A k → has-choice n B k
equiv-preserves-choice {n = n} {A} {B} (f , f-ise) A-hc C = is-eq to from to-from from-to where
  module f = is-equiv f-ise

  A-unchoose = unchoose {n = n} {A} {C ∘ f}
  module A-unchoose = is-equiv (A-hc (C ∘ f))

  to = unchoose {n = n} {B} {C}

  from' : Trunc n (Π A (C ∘ f)) → Trunc n (Π B C)
  from' = Trunc-fmap (λ g' b → transport C (f.f-g b) (g' (f.g b)))

  from : Π B (Trunc n ∘ C) → Trunc n (Π B C)
  from g = from' (A-unchoose.g (g ∘ f))

  abstract
    to-from''' : ∀ (g-f' : Π A (C ∘ f)) {a a'} (path : f.g (f a) == a')
      → transport C (ap f path) (g-f' (f.g (f a))) == g-f' a'
    to-from''' g-f' idp = idp

    to-from'' : ∀ (g-f' : Π A (C ∘ f)) a
      → transport C (f.f-g (f a)) (g-f' (f.g (f a))) == g-f' a
    to-from'' g-f' a =
      transport C (f.f-g (f a)) (g-f' (f.g (f a)))
        =⟨ ! $ ap (λ p → transport C p (g-f' (f.g (f a)))) (f.adj a) ⟩
      transport C (ap f (f.g-f a)) (g-f' (f.g (f a)))
        =⟨ to-from''' g-f' (f.g-f a) ⟩
      g-f' a
        =∎

    to-from' : ∀ g a → to (from g) (f a) == A-unchoose (A-unchoose.g (g ∘ f)) a
    to-from' g a =
      Trunc-elim
        {P = λ g-f → to (from' g-f) (f a) == A-unchoose g-f a}
        (λ g-f' → ap [_] $ to-from'' g-f' a)
        (A-unchoose.g (g ∘ f))

    to-from : ∀ g → to (from g) == g
    to-from g = λ= λ b → transport
      (λ b → to (from g) b == g b)
      (f.f-g b)
      ( to (from g) (f (f.g b))
          =⟨ to-from' g (f.g b) ⟩
        A-unchoose (A-unchoose.g (g ∘ f)) (f.g b)
          =⟨ app= (A-unchoose.f-g (g ∘ f)) (f.g b) ⟩
        g (f (f.g b))
          =∎)

    from-to' : ∀ g {b b'} (path : f (f.g b) == b')
      → transport C path (g (f (f.g b))) == g b'
    from-to' g idp = idp

    from-to : ∀ g → from (to g) == g
    from-to = Trunc-elim
      {P = λ g → from (to g) == g}
      (λ g →
        from' (A-unchoose.g (λ a → [ g (f a) ]))
          =⟨ ap from' (A-unchoose.g-f [ (g ∘ f) ]) ⟩
        from' [ (g ∘ f) ]
          =⟨ ap [_] $ λ= (λ b → from-to' g (f.f-g b)) ⟩
        [ g ]
          =∎)

Fin-has-choice : ∀ (n : ℕ₋₂) m l → has-choice n (Fin m) l
Fin-has-choice _ 0 _ = equiv-preserves-choice
  (Fin-equiv-Empty ⁻¹) Empty-has-choice
Fin-has-choice n (S m) l = equiv-preserves-choice
  (Fin-equiv-Coprod ⁻¹) (Coprod-has-choice (Fin-has-choice n m l) Unit-has-choice)
