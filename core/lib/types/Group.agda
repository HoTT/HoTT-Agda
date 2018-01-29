{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Fin
open import lib.types.Nat
open import lib.types.Int
open import lib.types.Pi

module lib.types.Group where

-- 1-approximation of groups without higher coherence conditions.
record GroupStructure {i} (El : Type i) --(El-level : has-level 0 El)
  : Type i where
  constructor group-structure
  field
    ident  : El
    inv    : El → El
    comp   : El → El → El
    unit-l : ∀ a → comp ident a == a
    assoc  : ∀ a b c → comp (comp a b) c == comp a (comp b c)
    inv-l  : ∀ a → (comp (inv a) a) == ident

  ⊙El : Ptd i
  ⊙El = ⊙[ El , ident ]

  private
    infix 80 _⊙_
    _⊙_ = comp

  abstract
    inv-r  : ∀ g → g ⊙ inv g == ident
    inv-r g =
      g ⊙ inv g                           =⟨ ! $ unit-l (g ⊙ inv g) ⟩
      ident ⊙ (g ⊙ inv g)                 =⟨ ! $ inv-l (inv g) |in-ctx _⊙ (g ⊙ inv g) ⟩
      (inv (inv g) ⊙ inv g) ⊙ (g ⊙ inv g) =⟨ assoc (inv (inv g)) (inv g) (g ⊙ inv g) ⟩
      inv (inv g) ⊙ (inv g ⊙ (g ⊙ inv g)) =⟨ ! $ assoc (inv g) g (inv g) |in-ctx inv (inv g) ⊙_ ⟩
      inv (inv g) ⊙ ((inv g ⊙ g) ⊙ inv g) =⟨ inv-l g |in-ctx (λ h → inv (inv g) ⊙ (h ⊙ inv g)) ⟩
      inv (inv g) ⊙ (ident ⊙ inv g)       =⟨ unit-l (inv g) |in-ctx inv (inv g) ⊙_ ⟩
      inv (inv g) ⊙ inv g                 =⟨ inv-l (inv g) ⟩
      ident                               =∎

    unit-r : ∀ g → g ⊙ ident == g
    unit-r g =
      g ⊙ ident          =⟨ ! (inv-l g) |in-ctx g ⊙_ ⟩
      g ⊙ (inv g ⊙ g)    =⟨ ! $ assoc g (inv g) g ⟩
      (g ⊙ inv g) ⊙ g    =⟨ inv-r g |in-ctx _⊙ g ⟩
      ident ⊙ g          =⟨ unit-l g ⟩
      g                  =∎

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

    inv-is-inj : is-inj inv
    inv-is-inj g₁ g₂ p = ! (inv-inv g₁) ∙ ap inv p ∙ inv-inv g₂

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

  conj : El → El → El
  conj g₁ g₂ = (g₁ ⊙ g₂) ⊙ inv g₁

  abstract
    conj-ident-r : ∀ g → conj g ident == ident
    conj-ident-r g = ap (_⊙ inv g) (unit-r _) ∙ inv-r g
  {- NOT USED
  abstract
    conj-unit-l : ∀ g → conj ident g == g
    conj-unit-l g = ap2 _⊙_ (unit-l _) inv-ident ∙ unit-r _

    conj-comp-l : ∀ g₁ g₂ g₃ → conj (g₁ ⊙ g₂) g₃ == conj g₁ (conj g₂ g₃)
    conj-comp-l g₁ g₂ g₃ =
      ((g₁ ⊙ g₂) ⊙ g₃) ⊙ inv (g₁ ⊙ g₂)
        =⟨ ap2 _⊙_ (assoc g₁ g₂ g₃) (inv-comp g₁ g₂) ⟩
      (g₁ ⊙ (g₂ ⊙ g₃)) ⊙ (inv g₂ ⊙ inv g₁)
        =⟨ ! $ assoc (g₁ ⊙ (g₂ ⊙ g₃)) (inv g₂) (inv g₁) ⟩
      ((g₁ ⊙ (g₂ ⊙ g₃)) ⊙ inv g₂) ⊙ inv g₁
        =⟨ assoc g₁ (g₂ ⊙ g₃) (inv g₂) |in-ctx _⊙ inv g₁ ⟩
      (g₁ ⊙ ((g₂ ⊙ g₃) ⊙ inv g₂)) ⊙ inv g₁
        =∎

    inv-conj : ∀ g₁ g₂ → inv (conj g₁ g₂) == conj g₁ (inv g₂)
    inv-conj g₁ g₂ = inv-comp (g₁ ⊙ g₂) (inv g₁)
                   ∙ ap2 _⊙_ (inv-inv g₁) (inv-comp g₁ g₂)
                   ∙ ! (assoc g₁ (inv g₂) (inv g₁))
  -}

  exp : El → ℤ → El
  exp g (pos 0) = ident
  exp g (pos 1) = g
  exp g (pos (S (S n))) = comp g (exp g (pos (S n)))
  exp g (negsucc 0) = inv g
  exp g (negsucc (S n)) = comp (inv g) (exp g (negsucc n))

  abstract
    exp-succ : ∀ g z → exp g (succ z) == comp g (exp g z)
    exp-succ g (pos 0) = ! (unit-r g)
    exp-succ g (pos 1) = idp
    exp-succ g (pos (S (S n))) = idp
    exp-succ g (negsucc 0) = ! (inv-r g)
    exp-succ g (negsucc (S n)) =
      ! (unit-l (exp g (negsucc n)))
      ∙ ap (λ h → comp h (exp g (negsucc n))) (! (inv-r g))
      ∙ assoc g (inv g) (exp g (negsucc n))

    exp-pred : ∀ g z → exp g (pred z) == comp (inv g) (exp g z)
    exp-pred g (pos 0) = ! (unit-r (inv g))
    exp-pred g (pos 1) = ! (inv-l g)
    exp-pred g (pos (S (S n))) =
      ! (unit-l (exp g (pos (S n))))
      ∙ ap (λ h → comp h (exp g (pos (S n)))) (! (inv-l g))
      ∙ assoc (inv g) g (exp g (pos (S n)))
    exp-pred g (negsucc 0) = idp
    exp-pred g (negsucc (S n)) = idp

    exp-+ : ∀ g z₁ z₂ → exp g (z₁ ℤ+ z₂) == comp (exp g z₁) (exp g z₂)
    exp-+ g (pos 0) z₂ = ! (unit-l _)
    exp-+ g (pos 1) z₂ = exp-succ g z₂
    exp-+ g (pos (S (S n))) z₂ =
      exp-succ g (pos (S n) ℤ+ z₂)
      ∙ ap (comp g) (exp-+ g (pos (S n)) z₂)
      ∙ ! (assoc g (exp g (pos (S n))) (exp g z₂))
    exp-+ g (negsucc 0) z₂ = exp-pred g z₂
    exp-+ g (negsucc (S n)) z₂ =
      exp-pred g (negsucc n ℤ+ z₂)
      ∙ ap (comp (inv g)) (exp-+ g (negsucc n) z₂)
      ∙ ! (assoc (inv g) (exp g (negsucc n)) (exp g z₂))

  diff : El → El → El
  diff g h = g ⊙ inv h

  abstract
    zero-diff-same : (g h : El) → diff g h == ident → g == h
    zero-diff-same g h p = inv-is-inj g h $ inv-unique-r g (inv h) p

    inv-diff : (g h : El) → inv (diff g h) == diff h g
    inv-diff g h = inv-comp g (inv h) ∙ ap (_⊙ inv g) (inv-inv h)

  sum : ∀ {I : ℕ} → (Fin I → El) → El
  sum {I = O} f = ident
  sum {I = S n} f = comp (sum (f ∘ Fin-S)) (f (n , ltS))

record Group i : Type (lsucc i) where
  constructor group
  field
    El : Type i
    {{El-level}} : has-level 0 El
    group-struct : GroupStructure El
  open GroupStructure group-struct public

Group₀ : Type (lsucc lzero)
Group₀ = Group lzero

is-abelian : ∀ {i} → Group i → Type i
is-abelian G = (a b : Group.El G) → Group.comp G a b == Group.comp G b a

AbGroup : ∀ i → Type (lsucc i)
AbGroup i = Σ (Group i) is-abelian

AbGroup₀ : Type (lsucc lzero)
AbGroup₀ = AbGroup lzero

module AbGroup {i} (G : AbGroup i) where
  grp = fst G
  comm = snd G
  open Group grp public

  abstract
    interchange : (g₁ g₂ g₃ g₄ : El) →
        comp (comp g₁ g₂) (comp g₃ g₄)
        == comp (comp g₁ g₃) (comp g₂ g₄)
    interchange g₁ g₂ g₃ g₄ =
      comp (comp g₁ g₂) (comp g₃ g₄)
        =⟨ assoc g₁ g₂ (comp g₃ g₄) ⟩
      comp g₁ (comp g₂ (comp g₃ g₄))
        =⟨ comm g₃ g₄ |in-ctx (λ g → (comp g₁ (comp g₂ g))) ⟩
      comp g₁ (comp g₂ (comp g₄ g₃))
        =⟨ ! (assoc g₂ g₄ g₃) |in-ctx comp g₁ ⟩
      comp g₁ (comp (comp g₂ g₄) g₃)
        =⟨ comm (comp g₂ g₄) g₃ |in-ctx comp g₁ ⟩
      comp g₁ (comp g₃ (comp g₂ g₄))
        =⟨ ! (assoc g₁ g₃ (comp g₂ g₄)) ⟩
      comp (comp g₁ g₃) (comp g₂ g₄)
        =∎

    diff-comp : (g₁ g₂ g₃ g₄ : El) →
        diff (comp g₁ g₂) (comp g₃ g₄)
        == comp (diff g₁ g₃) (diff g₂ g₄)
    diff-comp g₁ g₂ g₃ g₄ =
        diff (comp g₁ g₂) (comp g₃ g₄)
          =⟨ ap (comp (comp g₁ g₂)) (inv-comp g₃ g₄ ∙ comm (inv g₄) (inv g₃)) ⟩
        comp (comp g₁ g₂) (comp (inv g₃) (inv g₄))
          =⟨ interchange g₁ g₂ (inv g₃) (inv g₄) ⟩
        comp (diff g₁ g₃) (diff g₂ g₄)
          =∎

is-trivialᴳ : ∀ {i} (G : Group i) → Type i
is-trivialᴳ G = ∀ g → g == Group.ident G

contr-is-trivialᴳ : ∀ {i} (G : Group i)
  {{_ : is-contr (Group.El G)}} → is-trivialᴳ G
contr-is-trivialᴳ G g =
  contr-has-all-paths _ _

{- group-structure= -}

module _ where
  open GroupStructure

  abstract
    group-structure= : ∀ {i} {A : Type i} {{_ : is-set A}}
      {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
      → ∀ {unit-l₁ unit-l₂ assoc₁ assoc₂ inv-l₁ inv-l₂}
      → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
      → Path {A = GroupStructure A}
          (group-structure id₁ inv₁ comp₁ unit-l₁ assoc₁ inv-l₁)
          (group-structure id₂ inv₂ comp₂ unit-l₂ assoc₂ inv-l₂)
    group-structure= {id₁ = id₁} {inv₁ = inv₁} {comp₁ = comp₁} idp idp idp =
      ap3 (group-structure id₁ inv₁ comp₁)
        (prop-has-all-paths _ _)
        (prop-has-all-paths _ _)
        (prop-has-all-paths _ _)

    ↓-group-structure= : ∀ {i} {A B : Type i}
      {{_ : has-level 0 A}}
      {GS : GroupStructure A} {HS : GroupStructure B} (p : A == B)
      → (ident GS == ident HS [ (λ C → C) ↓ p ])
      → (inv GS == inv HS [ (λ C → C → C) ↓ p ])
      → (comp GS == comp HS [ (λ C → C → C → C) ↓ p ])
      → GS == HS [ GroupStructure ↓ p ]
    ↓-group-structure= idp = group-structure=
