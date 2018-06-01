{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Paths where

{- ! is an equivalence and works on ≠ -}
module _ {i} {A : Type i} {x y : A} where

  !-equiv : (x == y) ≃ (y == x)
  !-equiv = equiv ! ! !-! !-!

  ≠-inv : (x ≠ y) → (y ≠ x)
  ≠-inv x≠y y=x = x≠y (! y=x)

{- Pre- and post- concatenation are equivalences -}
module _ {i} {A : Type i} {x y z : A} where

  pre∙-is-equiv : (p : x == y) → is-equiv (λ (q : y == z) → p ∙ q)
  pre∙-is-equiv p = is-eq (λ q → p ∙ q) (λ r → ! p ∙ r) f-g g-f
    where f-g : ∀ r → p ∙ ! p ∙ r == r
          f-g r = ! (∙-assoc p (! p) r) ∙ ap (λ s → s ∙ r) (!-inv-r p)

          g-f : ∀ q → ! p ∙ p ∙ q == q
          g-f q = ! (∙-assoc (! p) p q) ∙ ap (λ s → s ∙ q) (!-inv-l p)

  pre∙-equiv : (p : x == y) → (y == z) ≃ (x == z)
  pre∙-equiv p = ((λ q → p ∙ q) , pre∙-is-equiv p)

  post∙-is-equiv : (p : y == z) → is-equiv (λ (q : x == y) → q ∙ p)
  post∙-is-equiv p = is-eq (λ q → q ∙ p) (λ r → r ∙ ! p) f-g g-f
    where f-g : ∀ r → (r ∙ ! p) ∙ p == r
          f-g r = ∙-assoc r (! p) p ∙ ap (λ s → r ∙ s) (!-inv-l p) ∙ ∙-unit-r r

          g-f : ∀ q → (q ∙ p) ∙ ! p == q
          g-f q = ∙-assoc q p (! p) ∙ ap (λ s → q ∙ s) (!-inv-r p) ∙ ∙-unit-r q

  post∙-equiv : (p : y == z) → (x == y) ≃ (x == z)
  post∙-equiv p = ((λ q → q ∙ p) , post∙-is-equiv p)

  pre∙'-is-equiv : (p : x == y) → is-equiv (λ (q : y == z) → p ∙' q)
  pre∙'-is-equiv p = is-eq (λ q → p ∙' q) (λ r → ! p ∙' r) f-g g-f
    where f-g : ∀ r → p ∙' ! p ∙' r == r
          f-g r = ! (∙'-assoc p (! p) r) ∙ ap (λ s → s ∙' r) (!-inv'-r p)
                  ∙ ∙'-unit-l r

          g-f : ∀ q → ! p ∙' p ∙' q == q
          g-f q = ! (∙'-assoc (! p) p q) ∙ ap (λ s → s ∙' q) (!-inv'-l p)
                  ∙ ∙'-unit-l q

  pre∙'-equiv : (p : x == y) → (y == z) ≃ (x == z)
  pre∙'-equiv p = ((λ q → p ∙' q) , pre∙'-is-equiv p)

  post∙'-is-equiv : (p : y == z) → is-equiv (λ (q : x == y) → q ∙' p)
  post∙'-is-equiv p = is-eq (λ q → q ∙' p) (λ r → r ∙' ! p) f-g g-f
    where f-g : ∀ r → (r ∙' ! p) ∙' p == r
          f-g r = ∙'-assoc r (! p) p ∙ ap (λ s → r ∙' s) (!-inv'-l p)

          g-f : ∀ q → (q ∙' p) ∙' ! p == q
          g-f q = ∙'-assoc q p (! p) ∙ ap (λ s → q ∙' s) (!-inv'-r p)

  post∙'-equiv : (p : y == z) → (x == y) ≃ (x == z)
  post∙'-equiv p = ((λ q → q ∙' p) , post∙'-is-equiv p)

module _ {i j} {A : Type i} {B : Type j}
  {f : A → B} {x y : A} {b : B} where

  ↓-app=cst-in : {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙ v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-in {p = idp} q = q

  ↓-app=cst-out : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙ v)
  ↓-app=cst-out {p = idp} r = r

  ↓-app=cst-β : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == (ap f p ∙ v))
    → ↓-app=cst-out {p = p} (↓-app=cst-in q) == q
  ↓-app=cst-β {p = idp} q = idp

  ↓-app=cst-η : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == v [ (λ x → f x == b) ↓ p ])
    → ↓-app=cst-in (↓-app=cst-out q) == q
  ↓-app=cst-η {p = idp} q = idp

  ↓-app=cst-econv : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == (ap f p ∙ v)) ≃ (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-econv {p = p} = equiv ↓-app=cst-in ↓-app=cst-out
    (↓-app=cst-η {p = p}) (↓-app=cst-β {p = p})

  ↓-cst=app-in : {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙' ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-in {p = idp} q = q

  ↓-cst=app-out : {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙' ap f p) == v
  ↓-cst=app-out {p = idp} r = r

  ↓-cst=app-econv : {p : x == y} {u : b == f x} {v : b == f y}
    → ((u ∙' ap f p) == v) ≃ (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-econv {p = idp} = equiv ↓-cst=app-in ↓-cst=app-out
     (λ _ → idp) (λ _ → idp)

{- alternative versions -}

module _ {i j} {A : Type i} {B : Type j}
  {f : A → B} {x y : A} {b : B} where

  ↓-app=cst-in' : {p : x == y} {u : f x == b} {v : f y == b}
    → u == (ap f p ∙' v)
    → (u == v [ (λ x → f x == b) ↓ p ])
  ↓-app=cst-in' {p = idp} {v = idp} q = q

  ↓-app=cst-out' : {p : x == y} {u : f x == b} {v : f y == b}
    → (u == v [ (λ x → f x == b) ↓ p ])
    → u == (ap f p ∙' v)
  ↓-app=cst-out' {p = idp} {v = idp} r = r

  ↓-app=cst-β' : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == (ap f p ∙' v))
    → ↓-app=cst-out' {p = p} {v = v} (↓-app=cst-in' q) == q
  ↓-app=cst-β' {p = idp} {v = idp} q = idp

  ↓-app=cst-η' : {p : x == y} {u : f x == b} {v : f y == b}
    → (q : u == v [ (λ x → f x == b) ↓ p ])
    → ↓-app=cst-in' (↓-app=cst-out' q) == q
  ↓-app=cst-η' {p = idp} {v = idp} q = idp

  ↓-cst=app-in' : {p : x == y} {u : b == f x} {v : b == f y}
    → (u ∙ ap f p) == v
    → (u == v [ (λ x → b == f x) ↓ p ])
  ↓-cst=app-in' {p = idp} {u = idp} q = q

  ↓-cst=app-out' : {p : x == y} {u : b == f x} {v : b == f y}
    → (u == v [ (λ x → b == f x) ↓ p ])
    → (u ∙ ap f p) == v
  ↓-cst=app-out' {p = idp} {u = idp} r = r

module _ {i} {A : Type i} where

  ↓-app=idf-in : {f : A → A} {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u ∙' p == ap f p ∙ v
    → u == v [ (λ z → f z == z) ↓ p ]
  ↓-app=idf-in {p = idp} q = q

  ↓-app=idf-out : {f : A → A} {x y : A} {p : x == y}
    {u : f x == x} {v : f y == y}
    → u == v [ (λ z → f z == z) ↓ p ]
    → u ∙' p == ap f p ∙ v
  ↓-app=idf-out {p = idp} q = q

  ↓-cst=idf-in : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙' p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in {p = idp} q = q

  ↓-cst=idf-in' : {a : A} {x y : A} {p : x == y} {u : a == x} {v : a == y}
    → (u ∙ p) == v
    → (u == v [ (λ x → a == x) ↓ p ])
  ↓-cst=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ q

  ↓-idf=cst-in : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → u == p ∙ v
    → (u == v [ (λ x → x == a) ↓ p ])
  ↓-idf=cst-in {p = idp} q = q

  ↓-idf=cst-out : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → (u == v [ (λ x → x == a) ↓ p ])
    → u == p ∙ v
  ↓-idf=cst-out {p = idp} q = q

  ↓-idf=cst-in' : {a : A} {x y : A} {p : x == y} {u : x == a} {v : y == a}
    → u == p ∙' v
    → (u == v [ (λ x → x == a) ↓ p ])
  ↓-idf=cst-in' {p = idp} q = q ∙ ∙'-unit-l _

  ↓-idf=idf-in' : {x y : A} {p : x == y} {u : x == x} {v : y == y}
    → u ∙ p == p ∙' v
    → (u == v [ (λ x → x == x) ↓ p ])
  ↓-idf=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ q ∙ ∙'-unit-l _

  ↓-idf=idf-out' : {x y : A} {p : x == y} {u : x == x} {v : y == y}
    → (u == v [ (λ x → x == x) ↓ p ])
    → u ∙ p == p ∙' v
  ↓-idf=idf-out' {p = idp} q = ∙-unit-r _ ∙ q ∙ ! (∙'-unit-l _)

{- Nondependent identity type -}

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  ↓-='-in : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u ∙' ap g p) == (ap f p ∙ v)
    → (u == v [ (λ x → f x == g x) ↓ p ])
  ↓-='-in {p = idp} q = q

  ↓-='-out : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u == v [ (λ x → f x == g x) ↓ p ])
    → (u ∙' ap g p) == (ap f p ∙ v)
  ↓-='-out {p = idp} q = q

  ↓-='-in' : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u ∙ ap g p) == (ap f p ∙' v)
    → (u == v [ (λ x → f x == g x) ↓ p ])
  ↓-='-in' {p = idp} q = ! (∙-unit-r _) ∙ q ∙ (∙'-unit-l _)

  ↓-='-out' : ∀ {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u == v [ (λ x → f x == g x) ↓ p ])
    → (u ∙ ap g p) == (ap f p ∙' v)
  ↓-='-out' {p = idp} q = (∙-unit-r _) ∙ q ∙ ! (∙'-unit-l _)

  -- TODO: better name
  ↓-='-in'-∙ : ∀ {x y z : A} {p : x == y} {p' : y == z}
    (u : f x == g x) (v : f y == g y) (w : f z == g z)
    → u ∙ ap g p == ap f p ∙' v
    → v ∙ ap g p' == ap f p' ∙' w
    → u ∙ ap g (p ∙ p') == ap f (p ∙ p') ∙' w
  ↓-='-in'-∙ {p = idp} {p' = idp} u v w q q' =
    (q ∙ ∙'-unit-l v) ∙ ! (∙-unit-r v) ∙ q'
  {-
  ↓-='-in'-∙ {p = p} {p' = p'} u v w q q' =
    ap (u ∙_) (ap-∙ g p p') ∙
    ! (∙-assoc u (ap g p) (ap g p')) ∙
    ap (_∙ ap g p') (q ∙ ∙'=∙ (ap f p) v) ∙
    ∙-assoc (ap f p) v (ap g p') ∙
    ap (ap f p ∙_) q' ∙
    ! (∙-∙'-assoc (ap f p) (ap f p') w) ∙
    ap (_∙' w) (∙-ap f p p')
  -}

  -- TODO: better name
  ↓-='-in'-pres-comp : ∀ {x y z : A} {p : x == y} {p' : y == z}
    {u : f x == g x} {v : f y == g y} {w : f z == g z}
    (q : u ∙ ap g p == ap f p ∙' v) (q' : v ∙ ap g p' == ap f p' ∙' w)
    → ↓-='-in' {u = u} {v = w} (↓-='-in'-∙ u v w q q') ==
      ↓-='-in' {u = u} {v = v} q ∙ᵈ ↓-='-in' {u = v} {v = w} q'
  ↓-='-in'-pres-comp {p = idp} {p' = idp} {u} {v} {w} q q' =
    -- ! (∙-unit-r u) ∙ ↓-='-in'-∙ u v w q q' ∙ ∙'-unit-l w
    --   =⟨ ap (λ s → ! (∙-unit-r u) ∙ s ∙ ∙'-unit-l w) h ⟩
    ! (∙-unit-r u) ∙ ((q ∙ ∙'-unit-l v) ∙ ! (∙-unit-r v) ∙ q') ∙ ∙'-unit-l w
      =⟨ ap (! (∙-unit-r u) ∙_) (∙-assoc (q ∙ ∙'-unit-l v) (! (∙-unit-r v) ∙ q') (∙'-unit-l w)) ⟩
    ! (∙-unit-r u) ∙ (q ∙ ∙'-unit-l v) ∙ (! (∙-unit-r v) ∙ q') ∙ ∙'-unit-l w
      =⟨ ! (∙-assoc (! (∙-unit-r u)) (q ∙ ∙'-unit-l v) ((! (∙-unit-r v) ∙ q') ∙ ∙'-unit-l w)) ⟩
    (! (∙-unit-r u) ∙ q ∙ ∙'-unit-l v) ∙ (! (∙-unit-r v) ∙ q') ∙ ∙'-unit-l w
      =⟨ ap ((! (∙-unit-r u) ∙ q ∙ ∙'-unit-l v) ∙_) (∙-assoc (! (∙-unit-r v)) q' (∙'-unit-l w)) ⟩
    (! (∙-unit-r u) ∙ q ∙ ∙'-unit-l v) ∙ ! (∙-unit-r v) ∙ q' ∙ ∙'-unit-l w =∎
    -- where
    -- h : ↓-='-in'-∙ u v w q q' == q ∙ ∙'-unit-l v ∙ ! (∙-unit-r v) ∙ q'
    -- h =
    --   {!!}

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} where

  {- A pattern that proved useful when using the elimination principle of EM₁ to construct a
    (dependent) path -}
  abstract
    ↓-='-in'-weird : ∀ {x y z : A} {p : x == y} {p' : y == z} {p'' : x == z}
      (p-comp : p'' == p ∙ p')
      {u : f x == g x} {v : f y == g y} {w : f z == g z}
      (q : u ∙ ap g p == ap f p ∙' v) (q' : v ∙ ap g p' == ap f p' ∙' w)
      (q'' : u ∙ ap g p'' == ap f p'' ∙' w)
      → q'' ∙ ap (λ z → ap f z ∙' w) p-comp ==
        ap (λ z → u ∙ ap g z) p-comp ∙' ↓-='-in'-∙ {p = p} {p' = p'} u v w q q'
      → ↓-='-in' {u = u} {v = w} q'' ==
        ↓-='-in' {p = p} {u = u} {v = v} q ∙ᵈ ↓-='-in' {p = p'} {u = v} {v = w} q'
          [ (λ p → u == w [ (λ x → f x == g x) ↓ p ]) ↓ p-comp ]
    ↓-='-in'-weird p-comp q q' q'' e =
      ap↓ ↓-='-in' (↓-='-in' e) ▹ ↓-='-in'-pres-comp {f = f} {g = g} q q'

{- Identity type where the type is dependent -}

module _ {i j} {A : Type i} {B : A → Type j} {f g : Π A B} where

  abstract
    private
      ◃idp' = ◃idp {B = B}
      idp▹' = idp▹ {B = B}

    ↓-=-in : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → u ◃ apd f p == apd g p ▹ v
      → (u == v [ (λ x → g x == f x) ↓ p ])
    ↓-=-in {p = idp} {u} {v} q = ! (◃idp' u) ∙ q ∙ idp▹' v

    ↓-=-out : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (u == v [ (λ x → g x == f x) ↓ p ])
      → u ◃ apd f p == apd g p ▹ v
    ↓-=-out {p = idp} {u} {v} q = (◃idp' u) ∙ q ∙ ! (idp▹' v)

    ↓-=-in-β : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (q : u == v [ (λ x → g x == f x) ↓ p ])
      → ↓-=-in (↓-=-out q) == q
    ↓-=-in-β {p = idp} {u} {v} q =
      ! (◃idp' u) ∙ (◃idp' u ∙ q ∙ ! (idp▹' v)) ∙ idp▹' v
        =⟨ ap (! (◃idp' u) ∙_) (∙-assoc (◃idp' u) (q ∙ ! (idp▹' v)) (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ ! (idp▹' v)) ∙ idp▹' v
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ w) (∙-assoc q (! (idp▹' v)) (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ ! (idp▹' v) ∙ idp▹' v)
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ (q ∙ w)) (!-inv-l (idp▹' v)) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ q ∙ idp
        =⟨ ap (λ w → ! (◃idp' u) ∙ ◃idp' u ∙ w) (∙-unit-r q) ⟩
      ! (◃idp' u) ∙ ◃idp' u ∙ q
        =⟨ ! (∙-assoc (! (◃idp' u)) (◃idp' u) q) ⟩
      (! (◃idp' u) ∙ ◃idp' u) ∙ q
        =⟨ ap (_∙ q) (!-inv-l (◃idp' u)) ⟩
      q =∎

    ↓-=-out-η : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
      → (q : u ◃ apd f p == apd g p ▹ v)
      → q == ↓-=-out (↓-=-in q)
    ↓-=-out-η {p = idp} {u} {v} q = ! $
      ◃idp' u ∙ (! (◃idp' u) ∙ q ∙ idp▹' v) ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ w) (∙-assoc (! (◃idp' u)) (q ∙ idp▹' v) (! (idp▹' v))) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ (q ∙ idp▹' v) ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ w) (∙-assoc q (idp▹' v) (! (idp▹' v))) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ idp▹' v ∙ ! (idp▹' v)
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ w) (!-inv-r (idp▹' v)) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q ∙ idp
        =⟨ ap (λ w → ◃idp' u ∙ ! (◃idp' u) ∙ w) (∙-unit-r q) ⟩
      ◃idp' u ∙ ! (◃idp' u) ∙ q
        =⟨ ! (∙-assoc (◃idp' u) (! (◃idp' u)) q) ⟩
      (◃idp' u ∙ ! (◃idp' u)) ∙ q
        =⟨ ap (_∙ q) (!-inv-r (◃idp' u)) ⟩
      q =∎

  ↓-=-in-is-equiv : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
    → is-equiv (↓-=-in {p = p} {u = u} {v = v})
  ↓-=-in-is-equiv = is-eq _ ↓-=-out ↓-=-in-β λ q → ! (↓-=-out-η q)

  ↓-=-equiv : {x y : A} {p : x == y} {u : g x == f x} {v : g y == f y}
    → (u ◃ apd f p == apd g p ▹ v) ≃ (u == v [ (λ x → g x == f x) ↓ p ])
  ↓-=-equiv = ↓-=-in , ↓-=-in-is-equiv


-- Dependent path in a type of the form [λ x → g (f x) == x]
module _ {i j} {A : Type i} {B : Type j} (g : B → A) (f : A → B) where
  ↓-∘=idf-in' : {x y : A} {p : x == y} {u : g (f x) == x} {v : g (f y) == y}
    → ((ap g (ap f p) ∙' v) == (u ∙ p))
    → (u == v [ (λ x → g (f x) == x) ↓ p ])
  ↓-∘=idf-in' {p = idp} q = ! (∙-unit-r _) ∙ (! q) ∙ (∙'-unit-l _)

module _ {i} {A : Type i} where
  homotopy-naturality : ∀ {k} {B : Type k} (f g : A → B)
    (h : (x : A) → f x == g x) {x y : A} (p : x == y)
    → ap f p ∙ h y == h x ∙ ap g p
  homotopy-naturality f g h {x} {y} p =
    ∙=∙' (ap f p) (h y) ∙ ! (↓-='-out' {f = f} {g = g} {p = p} {u = h x} {v = h y} (apd h p))

  homotopy-naturality-to-idf : (f : A → A)
    (h : (x : A) → f x == x) {x y : A} (p : x == y)
    → ap f p ∙ h y == h x ∙ p
  homotopy-naturality-to-idf f h {x} {y} p =
    homotopy-naturality f (λ a → a) h p ∙ ap (λ w → h x ∙ w) (ap-idf p)

  homotopy-naturality-from-idf : (g : A → A)
    (h : (x : A) → x == g x) {x y : A} (p : x == y)
    → p ∙ h y == h x ∙ ap g p
  homotopy-naturality-from-idf g h {x} {y} p =
    ap (λ w → w ∙ h y) (! (ap-idf p)) ∙ homotopy-naturality (λ a → a) g h p

-- WIP, derive it from more primitive principles
-- ↓-∘=id-in f g {p = p} {u} {v} q =
--   ↓-=-in (u ◃ apd (λ x → g (f x)) p =⟨ apd-∘ f g p |in-ctx (λ t → u ◃ t) ⟩
--         u ◃ ↓-apd-out _ f p (apdd g p (apd f p)) =⟨ apdd-cst (λ _ b → g b) p (ap f p) (! (apd-nd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (apd (λ t → g (π₂ t)) (pair= p (apd f p))) =⟨ apd-∘ π₂ g (pair= p (apd f p)) |in-ctx (λ t → u ◃ ↓-apd-out _ f p t) ⟩
--         u ◃ ↓-apd-out _ f p (↓-apd-out _ π₂ (pair= p (apd f p)) (apdd g (pair= p (apd f p)) (apd π₂ (pair= p (apd f p))))) =⟨ {!!} ⟩
--         apd (λ x → x) p ▹ v ∎)

-- module _ {i j} {A : Type i} {B : Type j} {x y z : A → B} where

--   lhs :
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     (α : q == q'            [ (λ a → x a == y a) ↓ p ])
--     (β : r ∙ ap z p == ap y p ∙' r')
--     → (q ∙' r) ∙ ap z p == ap x p ∙' q' ∙' r'
--   lhs =
--     (q ∙' r) ∙ ap z p     =⟨ ? ⟩  -- assoc
--     q ∙' (r ∙ ap z p)     =⟨ ? ⟩  -- β
--     q ∙' (ap y p ∙' r')   =⟨ ? ⟩  -- assoc
--     (q ∙' ap y p) ∙' r'   =⟨ ? ⟩  -- ∙ = ∙'
--     (q ∙ ap y p) ∙' r'    =⟨ ? ⟩  -- α
--     (ap x p ∙' q') ∙' r'  =⟨ ? ⟩  -- assoc
--     ap x p ∙' q' ∙' r' ∎


--   thing :
--     {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
--     {r : y a == z a} {r' : y a' == z a'}
--     (α : q == q'            [ (λ a → x a == y a) ↓ p ])
--     (β : r ∙ ap z p == ap y p ∙' r')
--     → (_∙'2ᵈ_ {r = r} {r' = r'} α (↓-='-in' β) == ↓-='-in' {!!})
--   thing = {!!}
