{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.PathSeq
open import lib.types.Paths using (homotopy-naturality)
open import lib.types.Group
open import lib.groups.Homomorphism

module lib.types.TwoGroupoid where

module _ {i j} {El : Type i} (Arr : El → El → Type j)
  (_ : ∀ x y → has-level 1 (Arr x y)) where

  record TwoOneSemiCategoryStructure : Type (lmax i j) where
    field
      comp : ∀ {x y z} → Arr x y → Arr y z → Arr x z
      assoc : ∀ {x y z w} (a : Arr x y) (b : Arr y z) (c : Arr z w)
        → comp (comp a b) c == comp a (comp b c)
      {- coherence -}
      pentagon-identity : ∀ {v w x y z} (a : Arr v w) (b : Arr w x) (c : Arr x y) (d : Arr y z)
        → assoc (comp a b) c d ∙ assoc a b (comp c d)
          == ap (λ s → comp s d) (assoc a b c) ∙ assoc a (comp b c) d ∙ ap (comp a) (assoc b c d)

  record TwoGroupoidStructure (semi-cat-struct : TwoOneSemiCategoryStructure) : Type (lmax i j) where
    open TwoOneSemiCategoryStructure semi-cat-struct public

    field
      ident : ∀ {x} → Arr x x
      inv : ∀ {x y} → Arr x y → Arr y x
      unit-l : ∀ {x y} (a : Arr x y) → comp ident a == a
      unit-r : ∀ {x y} (a : Arr x y) → comp a ident == a
      inv-l : ∀ {x y} (a : Arr x y) → comp (inv a) a == ident
      inv-r : ∀ {x y} (a : Arr x y) → comp a (inv a) == ident

    {-
    private
      infix 80 _⊙_
      _⊙_ = comp

    inv-r  : ∀ {x y} (a : Arr x y) → comp a (inv a) == ident
    inv-r a = ↯
      (a ⊙ inv a                          =⟪ ! $ unit-l (a ⊙ inv a) ⟫
      ident ⊙ (a ⊙ inv a)                 =⟪ ! $ inv-l (inv a) |in-ctx (λ x → x ⊙ (a ⊙ inv a)) ⟫
      (inv (inv a) ⊙ inv a) ⊙ (a ⊙ inv a) =⟪ assoc (inv (inv a)) (inv a) (a ⊙ inv a) ⟫
      inv (inv a) ⊙ (inv a ⊙ (a ⊙ inv a)) =⟪ ! $ assoc (inv a) a (inv a) |in-ctx (_⊙_ (inv (inv a))) ⟫
      inv (inv a) ⊙ ((inv a ⊙ a) ⊙ inv a) =⟪ inv-l a |in-ctx (λ h → inv (inv a) ⊙ (h ⊙ inv a)) ⟫
      inv (inv a) ⊙ (ident ⊙ inv a)       =⟪ unit-l (inv a) |in-ctx (_⊙_ (inv (inv a))) ⟫
      inv (inv a) ⊙ inv a                 =⟪ inv-l (inv a) ⟫
      ident                               ∎∎)

    unit-r : ∀ {x y} (a : Arr x y) → comp a ident == a
    unit-r a = ↯
      (a ⊙ ident      =⟪ ! (inv-l a) |in-ctx (a ⊙_) ⟫
      a ⊙ (inv a ⊙ a) =⟪ ! $ assoc a (inv a) a ⟫
      (a ⊙ inv a) ⊙ a =⟪ inv-r a |in-ctx (_⊙ a) ⟫
      ident ⊙ a       =⟪ unit-l a ⟫
      a               ∎∎)
    -}

    {- coherence -}
    field
      triangle-identity : ∀ {x y z} (a : Arr x y) (b : Arr y z)
        → ap (λ s → comp s b) (unit-r a) == assoc a ident b ∙ ap (comp a) (unit-l b)

      inv-coherence : ∀ {x y} (a : Arr x y)
        → ap (λ s → comp s a) (inv-r a) ∙ unit-l a
          == assoc a (inv a) a ∙ ap (comp a) (inv-l a) ∙ unit-r a

record TwoOneSemiCategory i j : Type (lsucc (lmax i j)) where
  constructor two-one-semi-category
  field
    El : Type i
    Arr : El → El → Type j
    Arr-level : ∀ x y → has-level 1 (Arr x y)
    two-one-semi-cat-struct : TwoOneSemiCategoryStructure Arr Arr-level

  open TwoOneSemiCategoryStructure two-one-semi-cat-struct public

record PreTwoGroupoid i j : Type (lsucc (lmax i j)) where
  constructor two-groupoid
  field
    two-one-semi-cat : TwoOneSemiCategory i j

  open TwoOneSemiCategory two-one-semi-cat public using (El; Arr; Arr-level; two-one-semi-cat-struct)

  field
    two-groupoid-struct : TwoGroupoidStructure Arr Arr-level two-one-semi-cat-struct

  open TwoGroupoidStructure two-groupoid-struct public

record TwoOneSemiCategoryFunctor {i₁ j₁ i₂ j₂} (C : TwoOneSemiCategory i₁ j₁) (D : TwoOneSemiCategory i₂ j₂)
  : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  private
    module C = TwoOneSemiCategory C
    module D = TwoOneSemiCategory D
  field
    F₀ : C.El → D.El
    F₁ : {x y : C.El} → C.Arr x y → D.Arr (F₀ x) (F₀ y)
    pres-comp : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → F₁ (C.comp f g) == D.comp (F₁ f) (F₁ g)

  pres-comp-coh-seq₁ : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
    → PathSeq (F₁ (C.comp (C.comp f g) h)) (D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)))
  pres-comp-coh-seq₁ f g h =
    F₁ (C.comp (C.comp f g) h)
      =⟪ pres-comp (C.comp f g) h ⟫
    D.comp (F₁ (C.comp f g)) (F₁ h)
      =⟪ ap (λ s → D.comp s (F₁ h)) (pres-comp f g) ⟫
    D.comp (D.comp (F₁ f) (F₁ g)) (F₁ h)
      =⟪ D.assoc (F₁ f) (F₁ g) (F₁ h) ⟫
    D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)) ∎∎

  pres-comp-coh-seq₂ : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
    → PathSeq (F₁ (C.comp (C.comp f g) h)) (D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)))
  pres-comp-coh-seq₂ f g h =
    F₁ (C.comp (C.comp f g) h)
      =⟪ ap F₁ (C.assoc f g h) ⟫
    F₁ (C.comp f (C.comp g h))
      =⟪ pres-comp f (C.comp g h) ⟫
    D.comp (F₁ f) (F₁ (C.comp g h))
      =⟪ ap (D.comp (F₁ f)) (pres-comp g h) ⟫
    D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)) ∎∎

  field
    pres-comp-coh : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
      → pres-comp-coh-seq₁ f g h =↯= pres-comp-coh-seq₂ f g h

comp-semi-cat-functors : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
  {C : TwoOneSemiCategory i₁ j₁} {D : TwoOneSemiCategory i₂ j₂} {E : TwoOneSemiCategory i₃ j₃}
  (F : TwoOneSemiCategoryFunctor C D) (G : TwoOneSemiCategoryFunctor D E)
  → TwoOneSemiCategoryFunctor C E
comp-semi-cat-functors {C = C} {D = D} {E = E} F G =
  record { F₀ = F₀; F₁ = F₁; pres-comp = pres-comp; pres-comp-coh = pres-comp-coh }
  where
    module C = TwoOneSemiCategory C
    module D = TwoOneSemiCategory D
    module E = TwoOneSemiCategory E
    module F = TwoOneSemiCategoryFunctor F
    module G = TwoOneSemiCategoryFunctor G
    F₀ : C.El → E.El
    F₀ = G.F₀ ∘ F.F₀
    F₁ : {x y : C.El} → C.Arr x y → E.Arr (F₀ x) (F₀ y)
    F₁ f = G.F₁ (F.F₁ f)
    pres-comp↯ : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → G.F₁ (F.F₁ (C.comp f g)) =-= E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g))
    pres-comp↯ f g =
      G.F₁ (F.F₁ (C.comp f g))
        =⟪ ap G.F₁ (F.pres-comp f g) ⟫
      G.F₁ (D.comp (F.F₁ f) (F.F₁ g))
        =⟪ G.pres-comp (F.F₁ f) (F.F₁ g) ⟫
      E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g)) ∎∎
    pres-comp : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → G.F₁ (F.F₁ (C.comp f g)) == E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g))
    pres-comp f g = ↯ (pres-comp↯ f g)
    pres-comp-coh : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
      → pres-comp (C.comp f g) h ∙ ap (λ s → E.comp s (F₁ h)) (pres-comp f g) ∙ E.assoc (F₁ f) (F₁ g) (F₁ h)
        == ap F₁ (C.assoc f g h) ∙ pres-comp f (C.comp g h) ∙ ap (E.comp (F₁ f)) (pres-comp g h)
    pres-comp-coh f g h =
      (pres-comp (C.comp f g) h ◃∙ ap (λ s → E.comp s (F₁ h)) (pres-comp f g) ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 0 & 1 & pres-comp↯ (C.comp f g) h & idp ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h)
      ◃∙ ap (λ s → E.comp s (F₁ h)) (pres-comp f g)
      ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 1 & ap-seq (λ s → E.comp s (F₁ h)) (pres-comp↯ f g)
                   & ap-seq-∙ (λ s → E.comp s (F₁ h)) (pres-comp↯ f g) ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h)
      ◃∙ ap (λ s → E.comp s (F₁ h)) (ap G.F₁ (F.pres-comp f g))
      ◃∙ ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g))
      ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 1 & ap (λ s → E.comp (G.F₁ s) (F₁ h)) (F.pres-comp f g) ◃∎
               & ∘-ap (λ s → E.comp s (F₁ h)) G.F₁ (F.pres-comp f g) ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h)
      ◃∙ ap (λ s → E.comp (G.F₁ s) (F₁ h)) (F.pres-comp f g)
      ◃∙ ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g))
      ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 1 & 2 & (ap (λ s → G.F₁ (D.comp s (F.F₁ h))) (F.pres-comp f g)
                    ◃∙ G.pres-comp (D.comp (F.F₁ f) (F.F₁ g)) (F.F₁ h) ◃∎)
               & ! (homotopy-naturality (λ s → G.F₁ (D.comp s (F.F₁ h)))
                                        (λ s → E.comp (G.F₁ s) (F₁ h))
                                        (λ s → G.pres-comp s (F.F₁ h))
                                        (F.pres-comp f g)) ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ ap (λ s → G.F₁ (D.comp s (F.F₁ h))) (F.pres-comp f g)
      ◃∙ G.pres-comp (D.comp (F.F₁ f) (F.F₁ g)) (F.F₁ h)
      ◃∙ ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g))
      ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 3 & (ap G.F₁ (D.assoc (F.F₁ f) (F.F₁ g) (F.F₁ h))
                     ◃∙ G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h))
                     ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
               & G.pres-comp-coh (F.F₁ f) (F.F₁ g) (F.F₁ h) ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ ap (λ s → G.F₁ (D.comp s (F.F₁ h))) (F.pres-comp f g)
      ◃∙ ap G.F₁ (D.assoc (F.F₁ f) (F.F₁ g) (F.F₁ h))
      ◃∙ G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h))
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 1 & 1 & ap G.F₁ (ap (λ s → D.comp s (F.F₁ h)) (F.pres-comp f g)) ◃∎
               & ap-∘ G.F₁ (λ s → D.comp s (F.F₁ h)) (F.pres-comp f g) ⟩
      (ap G.F₁ (F.pres-comp (C.comp f g) h)
      ◃∙ ap G.F₁ (ap (λ s → D.comp s (F.F₁ h)) (F.pres-comp f g))
      ◃∙ ap G.F₁ (D.assoc (F.F₁ f) (F.F₁ g) (F.F₁ h))
      ◃∙ G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h))
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 0 & 3 & ap-seq G.F₁ (F.pres-comp-coh-seq₂ f g h)
               & ap-seq-=↯= G.F₁ (F.pres-comp-coh-seq₁ f g h)
                                 (F.pres-comp-coh-seq₂ f g h)
                                 (F.pres-comp-coh f g h) ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ ap G.F₁ (F.pres-comp f (C.comp g h))
      ◃∙ ap G.F₁ (ap (D.comp (F.F₁ f)) (F.pres-comp g h))
      ◃∙ G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h))
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 2 & 1 & ap (G.F₁ ∘ D.comp (F.F₁ f)) (F.pres-comp g h) ◃∎
               & ∘-ap G.F₁ (D.comp (F.F₁ f)) (F.pres-comp g h) ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ ap G.F₁ (F.pres-comp f (C.comp g h))
      ◃∙ ap (G.F₁ ∘ D.comp (F.F₁ f)) (F.pres-comp g h)
      ◃∙ G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h))
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 2 & 2 & G.pres-comp (F.F₁ f) (F.F₁ (C.comp g h))
                     ◃∙ ap (λ s → E.comp (F₁ f) (G.F₁ s)) (F.pres-comp g h) ◃∎
               & homotopy-naturality (G.F₁ ∘ D.comp (F.F₁ f))
                                     (E.comp (F₁ f) ∘ G.F₁)
                                     (G.pres-comp (F.F₁ f))
                                     (F.pres-comp g h) ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ ap G.F₁ (F.pres-comp f (C.comp g h))
      ◃∙ G.pres-comp (F.F₁ f) (F.F₁ (C.comp g h))
      ◃∙ ap (λ s → E.comp (F₁ f) (G.F₁ s)) (F.pres-comp g h)
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 1 & 2 & pres-comp f (C.comp g h) ◃∎ & idp ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ pres-comp f (C.comp g h)
      ◃∙ ap (λ s → E.comp (F₁ f) (G.F₁ s)) (F.pres-comp g h)
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 2 & 1 & ap (E.comp (F₁ f)) (ap G.F₁ (F.pres-comp g h)) ◃∎
               & ap-∘ (E.comp (F₁ f)) G.F₁ (F.pres-comp g h) ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ pres-comp f (C.comp g h)
      ◃∙ ap (E.comp (F₁ f)) (ap G.F₁ (F.pres-comp g h))
      ◃∙ ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎)
        =↯=⟨ 2 & 2 & ap (E.comp (F₁ f)) (pres-comp g h) ◃∎
               & ∙-ap-seq (E.comp (F₁ f)) (pres-comp↯ g h) ⟩
      (ap G.F₁ (ap F.F₁ (C.assoc f g h))
      ◃∙ pres-comp f (C.comp g h)
      ◃∙ ap (E.comp (F₁ f)) (pres-comp g h) ◃∎)
        =↯=⟨ 0 & 1 & ap F₁ (C.assoc f g h) ◃∎ & ∘-ap G.F₁ F.F₁ (C.assoc f g h) ⟩
      (ap F₁ (C.assoc f g h) ◃∙ pres-comp f (C.comp g h) ◃∙ ap (E.comp (F₁ f)) (pres-comp g h) ◃∎) ↯∎

record TwoGroupoidFunctor {i₁ j₁ i₂ j₂} (C : PreTwoGroupoid i₁ j₁) (D : PreTwoGroupoid i₂ j₂)
  : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  private
    module C = PreTwoGroupoid C
    module D = PreTwoGroupoid D
  field
    semi-cat-functor : TwoOneSemiCategoryFunctor C.two-one-semi-cat D.two-one-semi-cat

  open TwoOneSemiCategoryFunctor semi-cat-functor public

  field
    pres-ident : (x : C.El) → F₁ (C.ident {x}) == D.ident {F₀ x}

  unit-l-seq : {x y : C.El} (a : C.Arr x y)
    → F₁ (C.comp C.ident a) =-= F₁ a
  unit-l-seq {x} {y} a =
    F₁ (C.comp C.ident a)
      =⟪ pres-comp C.ident a ⟫
    D.comp (F₁ C.ident) (F₁ a)
      =⟪ ap (λ s → D.comp s (F₁ a)) (pres-ident x) ⟫
    D.comp D.ident (F₁ a)
      =⟪ D.unit-l (F₁ a) ⟫
    F₁ a ∎∎

  unit-r-seq : {x y : C.El} (a : C.Arr x y)
    → F₁ (C.comp a C.ident) =-= F₁ a
  unit-r-seq {x} {y} a =
    F₁ (C.comp a C.ident)
      =⟪ pres-comp a C.ident ⟫
    D.comp (F₁ a) (F₁ C.ident)
      =⟪ ap (D.comp (F₁ a)) (pres-ident y) ⟫
    D.comp (F₁ a) D.ident
      =⟪ D.unit-r (F₁ a) ⟫
    F₁ a ∎∎

  field
    unit-l-coh : {x y : C.El} (a : C.Arr x y) →
      ap F₁ (C.unit-l a) == (↯ unit-l-seq a)
    unit-r-coh : {x y : C.El} (a : C.Arr x y) →
      ap F₁ (C.unit-r a) == (↯ unit-r-seq a)

comp-two-groupoid-functors : ∀ {i₁ j₁ i₂ j₂ i₃ j₃}
  {C : PreTwoGroupoid i₁ j₁} {D : PreTwoGroupoid i₂ j₂} {E : PreTwoGroupoid i₃ j₃}
  (F : TwoGroupoidFunctor C D) (G : TwoGroupoidFunctor D E)
  → TwoGroupoidFunctor C E
comp-two-groupoid-functors {C = C} {D = D} {E = E} F G =
  record
  { semi-cat-functor = semi-cat-functor
  ; pres-ident = pres-ident
  ; unit-l-coh = unit-l-coh
  ; unit-r-coh = unit-r-coh
  }
  where
    module C = PreTwoGroupoid C
    module D = PreTwoGroupoid D
    module E = PreTwoGroupoid E
    module F = TwoGroupoidFunctor F
    module G = TwoGroupoidFunctor G
    semi-cat-functor : TwoOneSemiCategoryFunctor C.two-one-semi-cat E.two-one-semi-cat
    semi-cat-functor = comp-semi-cat-functors F.semi-cat-functor G.semi-cat-functor
    open TwoOneSemiCategoryFunctor semi-cat-functor
    pres-ident : (x : C.El) → F₁ (C.ident {x}) == E.ident {F₀ x}
    pres-ident x = ap G.F₁ (F.pres-ident x) ∙ G.pres-ident (F.F₀ x)
    unit-l-coh : {x y : C.El} (a : C.Arr x y)
      → ap F₁ (C.unit-l a) == pres-comp C.ident a ∙
                              ap (λ s → E.comp s (F₁ a)) (pres-ident x)
                              ∙ E.unit-l (F₁ a)
    unit-l-coh {x} {y} a =
      ap F₁ (C.unit-l a)
        =⟨ ap-∘ G.F₁ F.F₁ (C.unit-l a) ⟩
      ap G.F₁ (ap F.F₁ (C.unit-l a))
        =⟨ ap-seq-=↯= G.F₁ (ap F.F₁ (C.unit-l a) ◃∎)
                      (F.unit-l-seq a) (F.unit-l-coh a) ⟩
      ap-seq G.F₁ (F.unit-l-seq a)
        =↯=⟨ 2 & 1 & G.unit-l-seq (F.F₁ a) & G.unit-l-coh (F.F₁ a) ⟩
      (ap G.F₁ (F.pres-comp C.ident a)
      ◃∙ ap G.F₁ (ap (λ s → D.comp s (F.F₁ a)) (F.pres-ident x)) ◃∎)
      ∙∙ G.unit-l-seq (F.F₁ a)
        =↯=⟨ 1 & 1 & (ap (λ s → G.F₁ (D.comp s (F.F₁ a))) (F.pres-ident x) ◃∎)
               & ∘-ap G.F₁ (λ s → D.comp s (F.F₁ a)) (F.pres-ident x) ⟩
      (ap G.F₁ (F.pres-comp C.ident a)
      ◃∙ ap (λ s → G.F₁ (D.comp s (F.F₁ a))) (F.pres-ident x) ◃∎)
      ∙∙ G.unit-l-seq (F.F₁ a)
        =↯=⟨ 1 & 2 & (G.pres-comp (F.F₁ C.ident) (F.F₁ a)
                     ◃∙ ap (λ s → E.comp (G.F₁ s) (F₁ a)) (F.pres-ident x) ◃∎)
               & homotopy-naturality (λ s → G.F₁ (D.comp s (F.F₁ a)))
                                     (λ s → E.comp (G.F₁ s) (F₁ a))
                                     (λ s → G.pres-comp s (F.F₁ a))
                                     (F.pres-ident x) ⟩
      (ap G.F₁ (F.pres-comp C.ident a)
      ◃∙ G.pres-comp (F.F₁ C.ident) (F.F₁ a)
      ◃∙ ap (λ s → E.comp (G.F₁ s) (F₁ a)) (F.pres-ident x)
      ◃∙ ap (λ s → E.comp s (F₁ a)) (G.pres-ident (F.F₀ x))
      ◃∙ E.unit-l (F₁ a) ◃∎)
        =↯=⟨ 0 & 2 & pres-comp C.ident a ◃∎ & idp ⟩
      (pres-comp C.ident a
      ◃∙ ap (λ s → E.comp (G.F₁ s) (F₁ a)) (F.pres-ident x)
      ◃∙ ap (λ s → E.comp s (F₁ a)) (G.pres-ident (F.F₀ x))
      ◃∙ E.unit-l (F₁ a) ◃∎)
        =↯=⟨ 1 & 1 & ap (λ s → E.comp s (F₁ a)) (ap G.F₁ (F.pres-ident x)) ◃∎
               & ap-∘ (λ s → E.comp s (F₁ a)) G.F₁ (F.pres-ident x) ⟩
      (pres-comp C.ident a
      ◃∙ ap (λ s → E.comp s (F₁ a)) (ap G.F₁ (F.pres-ident x))
      ◃∙ ap (λ s → E.comp s (F₁ a)) (G.pres-ident (F.F₀ x))
      ◃∙ E.unit-l (F₁ a) ◃∎)
        =↯=⟨ 1 & 2 & ap (λ s → E.comp s (F₁ a)) (pres-ident x) ◃∎
               & ∙-ap (λ s → E.comp s (F₁ a))
                      (ap G.F₁ (F.pres-ident x))
                      (G.pres-ident (F.F₀ x)) ⟩
      (pres-comp C.ident a
      ◃∙ ap (λ s → E.comp s (F₁ a)) (pres-ident x)
      ◃∙ E.unit-l (F₁ a) ◃∎) ↯∎
    unit-r-coh : {x y : C.El} (a : C.Arr x y)
      → ap F₁ (C.unit-r a) == pres-comp a C.ident ∙
                              ap (E.comp (F₁ a)) (pres-ident y) ∙
                              E.unit-r (F₁ a)
    unit-r-coh {x} {y} a =
      ap F₁ (C.unit-r a)
        =⟨ ap-∘ G.F₁ F.F₁ (C.unit-r a) ⟩
      ap G.F₁ (ap F.F₁ (C.unit-r a))
        =⟨ ap-seq-=↯= G.F₁ (ap F.F₁ (C.unit-r a) ◃∎)
                      (F.unit-r-seq a) (F.unit-r-coh a) ⟩
      ap-seq G.F₁ (F.unit-r-seq a)
        =↯=⟨ 2 & 1 & G.unit-r-seq (F.F₁ a) & G.unit-r-coh (F.F₁ a) ⟩
      (ap G.F₁ (F.pres-comp a C.ident)
      ◃∙ ap G.F₁ (ap (D.comp (F.F₁ a)) (F.pres-ident y)) ◃∎)
      ∙∙ G.unit-r-seq (F.F₁ a)
        =↯=⟨ 1 & 1 & (ap (G.F₁ ∘ D.comp (F.F₁ a)) (F.pres-ident y) ◃∎)
               & ∘-ap G.F₁ (D.comp (F.F₁ a)) (F.pres-ident y) ⟩
      (ap G.F₁ (F.pres-comp a C.ident)
      ◃∙ ap (G.F₁ ∘ D.comp (F.F₁ a)) (F.pres-ident y) ◃∎)
      ∙∙ G.unit-r-seq (F.F₁ a)
        =↯=⟨ 1 & 2 & (G.pres-comp (F.F₁ a) (F.F₁ C.ident)
                     ◃∙ ap (E.comp (F₁ a) ∘ G.F₁) (F.pres-ident y) ◃∎)
               & homotopy-naturality (G.F₁ ∘ D.comp (F.F₁ a))
                                     (E.comp (F₁ a) ∘ G.F₁)
                                     (G.pres-comp (F.F₁ a))
                                     (F.pres-ident y) ⟩
      (ap G.F₁ (F.pres-comp a C.ident)
      ◃∙ G.pres-comp (F.F₁ a) (F.F₁ C.ident)
      ◃∙ ap (E.comp (F₁ a) ∘ G.F₁) (F.pres-ident y)
      ◃∙ ap (E.comp (F₁ a)) (G.pres-ident (F.F₀ y))
      ◃∙ E.unit-r (F₁ a) ◃∎)
        =↯=⟨ 0 & 2 & pres-comp a C.ident ◃∎ & idp ⟩
      (pres-comp a C.ident
      ◃∙ ap (E.comp (F₁ a) ∘ G.F₁) (F.pres-ident y)
      ◃∙ ap (E.comp (F₁ a)) (G.pres-ident (F.F₀ y))
      ◃∙ E.unit-r (F₁ a) ◃∎)
        =↯=⟨ 1 & 1 & ap (E.comp (F₁ a)) (ap G.F₁ (F.pres-ident y)) ◃∎
               & ap-∘ (E.comp (F₁ a)) G.F₁ (F.pres-ident y) ⟩
      (pres-comp a C.ident
      ◃∙ ap (E.comp (F₁ a)) (ap G.F₁ (F.pres-ident y))
      ◃∙ ap (E.comp (F₁ a)) (G.pres-ident (F.F₀ y))
      ◃∙ E.unit-r (F₁ a) ◃∎)
        =↯=⟨ 1 & 2 & ap (E.comp (F₁ a)) (pres-ident y) ◃∎
               & ∙-ap (E.comp (F₁ a))
                      (ap G.F₁ (F.pres-ident y))
                      (G.pres-ident (F.F₀ y)) ⟩
      (pres-comp a C.ident
      ◃∙ ap (E.comp (F₁ a)) (pres-ident y)
      ◃∙ E.unit-r (F₁ a) ◃∎) ↯∎

two-one-semi-cat-from-group : ∀ {i} → Group i → TwoOneSemiCategory lzero i
two-one-semi-cat-from-group G =
  record
  { El = ⊤
  ; Arr = λ _ _ → G.El
  ; Arr-level = λ _ _ → raise-level 0 G.El-level
  ; two-one-semi-cat-struct =
    record
    { comp = G.comp
    ; assoc = G.assoc
    ; pentagon-identity = λ _ _ _ _ → prop-path (has-level-apply G.El-level _ _) _ _
    }
  }
  where
    module G = Group G

semi-cat-functor-from-homomorphism : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → TwoOneSemiCategoryFunctor (two-one-semi-cat-from-group G) (two-one-semi-cat-from-group H)
semi-cat-functor-from-homomorphism {G = G} {H = H} φ =
  record
  { F₀ = idf ⊤
  ; F₁ = φ.f
  ; pres-comp = φ.pres-comp
  ; pres-comp-coh = λ _ _ _ → prop-path (has-level-apply H.El-level _ _) _ _
  }
  where
    module G = Group G
    module H = Group H
    module φ = GroupHom φ
