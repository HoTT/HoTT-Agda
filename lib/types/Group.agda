{-# OPTIONS --without-K #-} 

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Group where

record GroupStructure {i} (El : Type i) (El-level : has-level ⟨0⟩ El)
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
open GroupStructure

record Group i : Type (lsucc i) where 
  constructor group
  field
    El : Type i
    El-level : has-level ⟨0⟩ El
    group-struct : GroupStructure El El-level
open Group

Group₀ : Type (lsucc lzero)
Group₀ = Group lzero

is-abelian : ∀ {i} → Group i → Type i
is-abelian G = (a b : El G) → 
  comp (group-struct G) a b == comp (group-struct G) b a

record GroupHom {i j} (G : Group i) (H : Group j) 
  : Type (lsucc (lmax i j)) where
  constructor group-hom
  field
    f : El G → El H
    pres-ident : f (ident (group-struct G)) == (ident (group-struct H))
    pres-comp  : ∀ g1 g2 → f (comp (group-struct G) g1 g2) 
                           == comp (group-struct H) (f g1) (f g2)

grouphom-pres-inv : ∀ {i j} {G : Group i} {H : Group j} (h : GroupHom G H)
  (a : El G) → GroupHom.f h (inv (group-struct G) a) 
            == inv (group-struct H) (GroupHom.f h a)
grouphom-pres-inv {G = G} {H = H} h a = 
  f (inv GS a)
    =⟨ ! (unitr HS (f (inv GS a))) ⟩
  comp HS (f (inv GS a)) (ident HS)
    =⟨ ! (invr HS (f a)) |in-ctx (λ w → comp HS (f (inv GS a)) w) ⟩
  comp HS (f (inv GS a)) (comp HS (f a) (inv HS (f a)))
    =⟨ ! (assoc HS (f (inv GS a)) (f a) (inv HS (f a))) ⟩
  comp HS (comp HS (f (inv GS a)) (f a)) (inv HS (f a))
    =⟨ lemma |in-ctx (λ w → comp HS w (inv HS (f a))) ⟩
  comp HS (ident HS) (inv HS (f a))
    =⟨ unitl HS (inv HS (f a)) ⟩
  inv HS (f a) ∎
  where 
  GS = group-struct G
  HS = group-struct H 
  f = GroupHom.f h

  lemma : comp HS (GroupHom.f h (inv GS a)) (GroupHom.f h a) == ident HS
  lemma = ! (GroupHom.pres-comp h (inv GS a) a) 
          ∙ ap (GroupHom.f h) (invl GS a) 
          ∙ GroupHom.pres-ident h

abstract
  group-structure= : ∀ {i} {A : Type i} {pA : has-level ⟨0⟩ A}
    {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
    → ∀ {unitl₁ unitl₂} → ∀ {unitr₁ unitr₂} → ∀ {assoc₁ assoc₂}
    → ∀ {invr₁ invr₂} → ∀ {invl₁ invl₂}
    → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
    → Path {A = GroupStructure A pA}
        (group-structure id₁ inv₁ comp₁ unitl₁ unitr₁ assoc₁ invl₁ invr₁)
        (group-structure id₂ inv₂ comp₂ unitl₂ unitr₂ assoc₂ invl₂ invr₂)
  group-structure= {A = A} {pA = pA} {id₁ = id₁} {inv₁ = inv₁} {comp₁ = comp₁} idp idp idp = 
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
    {A-level : has-level ⟨0⟩ A} {B-level : has-level ⟨0⟩ B}
    {GS : GroupStructure A A-level} {HS : GroupStructure B B-level}
    → (p : A == B) (q : A-level == B-level [ has-level ⟨0⟩ ↓ p ])
    → (ident GS == ident HS [ (λ C → C) ↓ p ]) 
    → (inv GS == inv HS [ (λ C → C → C) ↓ p ]) 
    → (comp GS == comp HS [ (λ C → C → C → C) ↓ p ])
    → GS == HS [ uncurry GroupStructure ↓ pair= p q ]
  ↓-group-structure= idp idp = group-structure=

  group-iso : ∀ {i} {G H : Group i} (h : GroupHom G H)
    → is-equiv (GroupHom.f h) → G == H
  group-iso {G = G} {H = H} h e = 
    lemma group 
      (ua (f , e))
      (prop-has-all-paths-↓ has-level-is-prop) 
      (↓-group-structure= (ua (f , e)) _ ident= inv= comp=)
    where
    open GroupHom h
    GS : GroupStructure (El G) (El-level G)
    GS = group-struct G
    HS : GroupStructure (El H) (El-level H)
    HS = group-struct H

    ident= : ident GS == ident HS [ (λ C → C) ↓ ua (f , e) ]
    ident= = ↓-idf-ua-in _ pres-ident

    inv= : inv GS == inv HS [ (λ C → C → C) ↓ ua (f , e) ]
    inv= =
      coe (↓-→-is-square (inv GS) (inv HS) (ua (f , e))) $ λ= $ λ a → 
        transport (λ C → C) (ua (f , e)) (inv GS a) 
          =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
        f (inv GS a) 
          =⟨ grouphom-pres-inv h a ⟩
        inv HS (f a)
          =⟨ ap (inv HS) (! (to-transp (↓-idf-ua-in _ idp))) ⟩
        inv HS (transport (λ C → C) (ua (f , e)) a) ∎

    comp=' : (a : El G) 
      → comp GS a == comp HS (f a) [ (λ C → C → C) ↓ ua (f , e) ]
    comp=' a = 
      coe (↓-→-is-square (comp GS a) (comp HS (f a)) (ua (f , e))) $ λ= $ λ b →
        transport (λ C → C) (ua (f , e)) (comp GS a b)
          =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
        f (comp GS a b)
          =⟨ pres-comp a b ⟩
        comp HS (f a) (f b)
          =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → comp HS (f a) w) ⟩
        comp HS (f a) (transport (λ C → C) (ua (f , e)) b) ∎

    comp= : comp GS == comp HS [ (λ C → C → C → C) ↓ ua (f , e) ]
    comp= =
      coe (↓-→-is-square (comp GS) (comp HS) (ua (f , e))) $ λ= $ λ a → 
        transport (λ C → C → C) (ua (f , e)) (comp GS a)
          =⟨ to-transp (comp=' a) ⟩
        comp HS (f a)
          =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → comp HS w) ⟩ 
        comp HS (transport (λ C → C) (ua (f , e)) a) ∎

    lemma : ∀ {i j k l} {C : Type i} {D : C → Type j} 
      {E : (c : C) → D c → Type k} {F : Type l}
      {c₁ c₂ : C} {d₁ : D c₁} {d₂ : D c₂} {e₁ : E c₁ d₁} {e₂ : E c₂ d₂}
      (f : (c : C) (d : D c) → E c d → F) (p : c₁ == c₂) 
      (q : d₁ == d₂ [ D ↓ p ]) → (e₁ == e₂ [ uncurry E ↓ pair= p q ])
      → (f c₁ d₁ e₁ == f c₂ d₂ e₂)
    lemma f idp idp idp = idp
