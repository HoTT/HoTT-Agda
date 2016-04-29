{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi

module lib.types.Group where

record GroupStructure {i} (El : Type i) --(El-level : has-level 0 El)
  : Type i where
  constructor group-structure
  field
    ident : El
    inv : El → El
    comp : El → El → El
    unitl : ∀ a → comp ident a == a
    unitr : ∀ a → comp a ident == a
    assoc   : ∀ a b c → comp (comp a b) c == comp a (comp b c)
    invl    : ∀ a → (comp (inv a) a) == ident
    invr    : ∀ a → (comp a (inv a)) == ident

record Group i : Type (lsucc i) where
  constructor group
  field
    El : Type i
    El-level : has-level 0 El
    group-struct : GroupStructure El
  open GroupStructure group-struct public

  ⊙El : Σ (Type i) (λ A → A)
  ⊙El = (El , ident)

Group₀ : Type (lsucc lzero)
Group₀ = Group lzero

is-abelian : ∀ {i} → Group i → Type i
is-abelian G = (a b : Group.El G) → Group.comp G a b == Group.comp G b a

module _ where
  open GroupStructure

  abstract
    group-structure= : ∀ {i} {A : Type i} (pA : has-level 0 A)
      {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
      → ∀ {unitl₁ unitl₂} → ∀ {unitr₁ unitr₂} → ∀ {assoc₁ assoc₂}
      → ∀ {invr₁ invr₂} → ∀ {invl₁ invl₂}
      → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
      → Path {A = GroupStructure A}
          (group-structure id₁ inv₁ comp₁ unitl₁ unitr₁ assoc₁ invl₁ invr₁)
          (group-structure id₂ inv₂ comp₂ unitl₂ unitr₂ assoc₂ invl₂ invr₂)
    group-structure= pA {id₁ = id₁} {inv₁ = inv₁} {comp₁ = comp₁} idp idp idp =
      ap5 (group-structure id₁ inv₁ comp₁)
        (prop-has-all-paths (Π-level (λ _ → pA _ _)) _ _)
        (prop-has-all-paths (Π-level (λ _ → pA _ _)) _ _)
        (prop-has-all-paths
          (Π-level (λ _ → Π-level (λ _ → Π-level (λ _ → pA _ _)))) _ _)
        (prop-has-all-paths (Π-level (λ _ → pA _ _)) _ _)
        (prop-has-all-paths (Π-level (λ _ → pA _ _)) _ _)
      where
      ap5 : ∀ {j} {C D E F G H : Type j}
        {c₁ c₂ : C} {d₁ d₂ : D} {e₁ e₂ : E} {f₁ f₂ : F} {g₁ g₂ : G}
        (f : C → D → E → F → G → H)
        → (c₁ == c₂) → (d₁ == d₂) → (e₁ == e₂) → (f₁ == f₂) → (g₁ == g₂)
        → f c₁ d₁ e₁ f₁ g₁ == f c₂ d₂ e₂ f₂ g₂
      ap5 f idp idp idp idp idp = idp

    ↓-group-structure= : ∀ {i} {A B : Type i}
      (A-level : has-level 0 A)
      {GS : GroupStructure A} {HS : GroupStructure B} (p : A == B)
      → (ident GS == ident HS [ (λ C → C) ↓ p ])
      → (inv GS == inv HS [ (λ C → C → C) ↓ p ])
      → (comp GS == comp HS [ (λ C → C → C → C) ↓ p ])
      → GS == HS [ GroupStructure ↓ p ]
    ↓-group-structure= A-level idp = group-structure= A-level

module _ {i} (G : Group i) where
  private
    open Group G
    infix 80 _⊙_
    _⊙_ = comp

  group-inv-unique-l : (g h : El) → (g ⊙ h == ident) → inv h == g
  group-inv-unique-l g h p =
    inv h              =⟨ ! (unitl (inv h)) ⟩
    ident ⊙ inv h      =⟨ ! p |in-ctx (λ w → w ⊙ inv h) ⟩
    (g ⊙ h) ⊙ inv h    =⟨ assoc g h (inv h) ⟩
    g ⊙ (h ⊙ inv h)    =⟨ invr h |in-ctx (λ w → g ⊙ w) ⟩
    g ⊙ ident          =⟨ unitr g ⟩
    g                     ∎

  group-inv-unique-r : (g h : El) → (g ⊙ h == ident) → inv g == h
  group-inv-unique-r g h p =
    inv g              =⟨ ! (unitr (inv g)) ⟩
    inv g ⊙ ident      =⟨ ! p |in-ctx (λ w → inv g ⊙ w) ⟩
    inv g ⊙ (g ⊙ h)    =⟨ ! (assoc (inv g) g h) ⟩
    (inv g ⊙ g) ⊙ h    =⟨ invl g |in-ctx (λ w → w ⊙ h) ⟩
    ident ⊙ h          =⟨ unitl h ⟩
    h                     ∎

  group-inv-ident : inv ident == ident
  group-inv-ident =
    group-inv-unique-l ident ident (unitl ident)

  group-inv-comp : (g₁ g₂ : El) → inv (g₁ ⊙ g₂) == inv g₂ ⊙ inv g₁
  group-inv-comp g₁ g₂ =
    group-inv-unique-r (g₁ ⊙ g₂) (inv g₂ ⊙ inv g₁) $
      (g₁ ⊙ g₂) ⊙ (inv g₂ ⊙ inv g₁)
        =⟨ assoc g₁ g₂ (inv g₂ ⊙ inv g₁) ⟩
      g₁ ⊙ (g₂ ⊙ (inv g₂ ⊙ inv g₁))
        =⟨ ! (assoc g₂ (inv g₂) (inv g₁)) |in-ctx (λ w → g₁ ⊙ w) ⟩
      g₁ ⊙ ((g₂ ⊙ inv g₂) ⊙ inv g₁)
        =⟨ invr g₂ |in-ctx (λ w → g₁ ⊙ (w ⊙ inv g₁)) ⟩
      g₁ ⊙ (ident ⊙ inv g₁)
        =⟨ unitl (inv g₁) |in-ctx (λ w → g₁ ⊙ w) ⟩
      g₁ ⊙ inv g₁
        =⟨ invr g₁ ⟩
      ident ∎

  group-inv-inv : (g : El) → inv (inv g) == g
  group-inv-inv g = group-inv-unique-r (inv g) g (invl g)

  group-cancel-l : (g : El) {h k : El} → g ⊙ h == g ⊙ k → h == k
  group-cancel-l g {h} {k} p =
    h                  =⟨ ! (unitl h) ⟩
    ident ⊙ h          =⟨ ap (λ w → w ⊙ h) (! (invl g)) ⟩
    (inv g ⊙ g) ⊙ h    =⟨ assoc (inv g) g h ⟩
    inv g ⊙ (g ⊙ h)    =⟨ ap (λ w → inv g ⊙ w) p ⟩
    inv g ⊙ (g ⊙ k)    =⟨ ! (assoc (inv g) g k) ⟩
    (inv g ⊙ g) ⊙ k    =⟨ ap (λ w → w ⊙ k) (invl g) ⟩
    ident ⊙ k          =⟨ unitl k ⟩
    k ∎

  group-cancel-r : (g : El) {h k : El} → h ⊙ g == k ⊙ g → h == k
  group-cancel-r g {h} {k} p =
    h                  =⟨ ! (unitr h) ⟩
    h ⊙ ident          =⟨ ap (λ w → h ⊙ w) (! (invr g)) ⟩
    h ⊙ (g ⊙ inv g)    =⟨ ! (assoc h g (inv g)) ⟩
    (h ⊙ g) ⊙ inv g    =⟨ ap (λ w → w ⊙ inv g) p ⟩
    (k ⊙ g) ⊙ inv g    =⟨ assoc k g (inv g) ⟩
    k ⊙ (g ⊙ inv g)    =⟨ ap (λ w → k ⊙ w) (invr g) ⟩
    k ⊙ ident          =⟨ unitr k ⟩
    k ∎
