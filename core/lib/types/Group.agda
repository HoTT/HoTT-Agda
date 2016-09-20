{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed

module lib.types.Group where

record GroupStructure {i} (El : Type i) --(El-level : has-level 0 El)
  : Type i where
  constructor group-structure
  field
    ident  : El
    inv    : El → El
    comp   : El → El → El
    unit-l : ∀ a → comp ident a == a
    unit-r : ∀ a → comp a ident == a
    assoc  : ∀ a b c → comp (comp a b) c == comp a (comp b c)
    inv-l  : ∀ a → (comp (inv a) a) == ident
    inv-r  : ∀ a → (comp a (inv a)) == ident

  ⊙El : Ptd i
  ⊙El = (El , ident)

  private
    infix 80 _⊙_
    _⊙_ = comp

  cong : El → El → El
  cong g₁ g₂ = (g₁ ⊙ g₂) ⊙ inv g₁

  abstract
    inv-unique-l : (g h : El) → (g ⊙ h == ident) → inv h == g
    inv-unique-l g h p =
      inv h              =⟨ ! (unit-l (inv h)) ⟩
      ident ⊙ inv h      =⟨ ! p |in-ctx (λ w → w ⊙ inv h) ⟩
      (g ⊙ h) ⊙ inv h    =⟨ assoc g h (inv h) ⟩
      g ⊙ (h ⊙ inv h)    =⟨ inv-r h |in-ctx (λ w → g ⊙ w) ⟩
      g ⊙ ident          =⟨ unit-r g ⟩
      g                  =∎

    inv-unique-r : (g h : El) → (g ⊙ h == ident) → inv g == h
    inv-unique-r g h p =
      inv g              =⟨ ! (unit-r (inv g)) ⟩
      inv g ⊙ ident      =⟨ ! p |in-ctx (λ w → inv g ⊙ w) ⟩
      inv g ⊙ (g ⊙ h)    =⟨ ! (assoc (inv g) g h) ⟩
      (inv g ⊙ g) ⊙ h    =⟨ inv-l g |in-ctx (λ w → w ⊙ h) ⟩
      ident ⊙ h          =⟨ unit-l h ⟩
      h                  =∎

    inv-ident : inv ident == ident
    inv-ident = inv-unique-l ident ident (unit-l ident)

    inv-comp : (g₁ g₂ : El) → inv (g₁ ⊙ g₂) == inv g₂ ⊙ inv g₁
    inv-comp g₁ g₂ =
      inv-unique-r (g₁ ⊙ g₂) (inv g₂ ⊙ inv g₁) $
        (g₁ ⊙ g₂) ⊙ (inv g₂ ⊙ inv g₁)
          =⟨ assoc g₁ g₂ (inv g₂ ⊙ inv g₁) ⟩
        g₁ ⊙ (g₂ ⊙ (inv g₂ ⊙ inv g₁))
          =⟨ ! (assoc g₂ (inv g₂) (inv g₁)) |in-ctx (λ w → g₁ ⊙ w) ⟩
        g₁ ⊙ ((g₂ ⊙ inv g₂) ⊙ inv g₁)
          =⟨ inv-r g₂ |in-ctx (λ w → g₁ ⊙ (w ⊙ inv g₁)) ⟩
        g₁ ⊙ (ident ⊙ inv g₁)
          =⟨ unit-l (inv g₁) |in-ctx (λ w → g₁ ⊙ w) ⟩
        g₁ ⊙ inv g₁
          =⟨ inv-r g₁ ⟩
        ident =∎

    inv-inv : (g : El) → inv (inv g) == g
    inv-inv g = inv-unique-r (inv g) g (inv-l g)

    cancel-l : (g : El) {h k : El} → g ⊙ h == g ⊙ k → h == k
    cancel-l g {h} {k} p =
      h                  =⟨ ! (unit-l h) ⟩
      ident ⊙ h          =⟨ ap (λ w → w ⊙ h) (! (inv-l g)) ⟩
      (inv g ⊙ g) ⊙ h    =⟨ assoc (inv g) g h ⟩
      inv g ⊙ (g ⊙ h)    =⟨ ap (λ w → inv g ⊙ w) p ⟩
      inv g ⊙ (g ⊙ k)    =⟨ ! (assoc (inv g) g k) ⟩
      (inv g ⊙ g) ⊙ k    =⟨ ap (λ w → w ⊙ k) (inv-l g) ⟩
      ident ⊙ k          =⟨ unit-l k ⟩
      k =∎

    cancel-r : (g : El) {h k : El} → h ⊙ g == k ⊙ g → h == k
    cancel-r g {h} {k} p =
      h                  =⟨ ! (unit-r h) ⟩
      h ⊙ ident          =⟨ ap (λ w → h ⊙ w) (! (inv-r g)) ⟩
      h ⊙ (g ⊙ inv g)    =⟨ ! (assoc h g (inv g)) ⟩
      (h ⊙ g) ⊙ inv g    =⟨ ap (λ w → w ⊙ inv g) p ⟩
      (k ⊙ g) ⊙ inv g    =⟨ assoc k g (inv g) ⟩
      k ⊙ (g ⊙ inv g)    =⟨ ap (λ w → k ⊙ w) (inv-r g) ⟩
      k ⊙ ident          =⟨ unit-r k ⟩
      k =∎

    {- NOT USED
    cong-unit-l : ∀ g → cong ident g == g
    cong-unit-l g = ap2 _⊙_ (unit-l _) inv-ident ∙ unit-r _

    cong-ident-r : ∀ g → cong g ident == ident
    cong-ident-r g = ap (_⊙ inv g) (unit-r _) ∙ inv-r g 

    cong-comp-l : ∀ g₁ g₂ g₃ → cong (g₁ ⊙ g₂) g₃ == cong g₁ (cong g₂ g₃)
    cong-comp-l g₁ g₂ g₃ =
      ((g₁ ⊙ g₂) ⊙ g₃) ⊙ inv (g₁ ⊙ g₂)
        =⟨ ap2 _⊙_ (assoc g₁ g₂ g₃) (inv-comp g₁ g₂) ⟩
      (g₁ ⊙ (g₂ ⊙ g₃)) ⊙ (inv g₂ ⊙ inv g₁)
        =⟨ ! $ assoc (g₁ ⊙ (g₂ ⊙ g₃)) (inv g₂) (inv g₁) ⟩
      ((g₁ ⊙ (g₂ ⊙ g₃)) ⊙ inv g₂) ⊙ inv g₁
        =⟨ assoc g₁ (g₂ ⊙ g₃) (inv g₂) |in-ctx _⊙ inv g₁ ⟩
      (g₁ ⊙ ((g₂ ⊙ g₃) ⊙ inv g₂)) ⊙ inv g₁
        =∎

    inv-cong : ∀ g₁ g₂ → inv (cong g₁ g₂) == cong g₁ (inv g₂)
    inv-cong g₁ g₂ = inv-comp (g₁ ⊙ g₂) (inv g₁)
                   ∙ ap2 _⊙_ (inv-inv g₁) (inv-comp g₁ g₂)
                   ∙ ! (assoc g₁ (inv g₂) (inv g₁))
    -}

record Group i : Type (lsucc i) where
  constructor group
  field
    El : Type i
    El-level : has-level 0 El
    group-struct : GroupStructure El
  open GroupStructure group-struct public
  El-is-set = El-level

Group₀ : Type (lsucc lzero)
Group₀ = Group lzero

is-abelian : ∀ {i} → Group i → Type i
is-abelian G = (a b : Group.El G) → Group.comp G a b == Group.comp G b a

AbelianGroup : ∀ i → Type (lsucc i)
AbelianGroup i = Σ (Group i) is-abelian

module AbelianGroup {i} (G : AbelianGroup i) where
  grp = fst G
  comm = snd G
  open Group grp public

module _ where
  open GroupStructure

  abstract
    group-structure= : ∀ {i} {A : Type i} (pA : has-level 0 A)
      {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
      → ∀ {unit-l₁ unit-l₂} → ∀ {unit-r₁ unit-r₂} → ∀ {assoc₁ assoc₂}
      → ∀ {inv-r₁ inv-r₂} → ∀ {inv-l₁ inv-l₂}
      → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
      → Path {A = GroupStructure A}
          (group-structure id₁ inv₁ comp₁ unit-l₁ unit-r₁ assoc₁ inv-l₁ inv-r₁)
          (group-structure id₂ inv₂ comp₂ unit-l₂ unit-r₂ assoc₂ inv-l₂ inv-r₂)
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
