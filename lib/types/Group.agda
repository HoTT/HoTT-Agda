{-# OPTIONS --without-K #-} 

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Sigma
open import lib.types.Pi

module lib.types.Group where

record GroupStructure {i} (El : Type i) --(El-level : has-level ⟨0⟩ El)
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
    group-struct : GroupStructure El

  Ptd-El : Σ (Type i) (λ A → A)
  Ptd-El = (El , GroupStructure.ident group-struct)

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

  ptd-f : Σ (El G → El H) 
            (λ f → f (ident (group-struct G)) == ident (group-struct H))
  ptd-f = (f , pres-ident)


idhom : ∀ {i} (G : Group i) → GroupHom G G
idhom G = group-hom (idf _) idp (λ _ _ → idp)

_∘hom_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → GroupHom H K → GroupHom G H → GroupHom G K
(group-hom g g-id g-comp) ∘hom (group-hom f f-id f-comp) =
  record {
    f = g ∘ f;
    pres-ident = ap g f-id ∙ g-id;
    pres-comp = λ x₁ x₂ → ap g (f-comp x₁ x₂) ∙ g-comp (f x₁) (f x₂)}

hom= : ∀ {i j} {G : Group i} {H : Group j} (h k : GroupHom G H)
  → GroupHom.f h == GroupHom.f k → h == k
hom= {H = H} (group-hom f f-id f-comp) (group-hom g g-id g-comp) p =
  ap (λ {(h , (h-id , h-comp)) → group-hom h h-id h-comp}) 
     (pair= p 
       (prop-has-all-paths-↓ 
         (×-level (Group.El-level H _ _) 
                  (Π-level (λ _ → Π-level (λ _ → Group.El-level H _ _))))))


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
  group-structure= : ∀ {i} {A : Type i} (pA : has-level ⟨0⟩ A)
    {id₁ id₂ : A} {inv₁ inv₂ : A → A} {comp₁ comp₂ : A → A → A}
    → ∀ {unitl₁ unitl₂} → ∀ {unitr₁ unitr₂} → ∀ {assoc₁ assoc₂}
    → ∀ {invr₁ invr₂} → ∀ {invl₁ invl₂}
    → (id₁ == id₂) → (inv₁ == inv₂) → (comp₁ == comp₂)
    → Path {A = GroupStructure A}
        (group-structure id₁ inv₁ comp₁ unitl₁ unitr₁ assoc₁ invl₁ invr₁)
        (group-structure id₂ inv₂ comp₂ unitl₂ unitr₂ assoc₂ invl₂ invr₂)
  group-structure= {A = A} pA {id₁ = id₁} {inv₁ = inv₁} {comp₁ = comp₁} idp idp idp = 
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
    (A-level : has-level ⟨0⟩ A) 
    {GS : GroupStructure A} {HS : GroupStructure B} (p : A == B) 
    → (ident GS == ident HS [ (λ C → C) ↓ p ]) 
    → (inv GS == inv HS [ (λ C → C → C) ↓ p ]) 
    → (comp GS == comp HS [ (λ C → C → C → C) ↓ p ])
    → GS == HS [ GroupStructure ↓ p ]
  ↓-group-structure= A-level idp = group-structure= A-level

  group-iso : ∀ {i} {G H : Group i} (h : GroupHom G H)
    → is-equiv (GroupHom.f h) → G == H
  group-iso {G = G} {H = H} h e =
    lemma group 
      (ua (f , e))
      (prop-has-all-paths-↓ has-level-is-prop) 
      (↓-group-structure= (Group.El-level G) (ua (f , e)) ident= inv= comp=)
    where
    open GroupHom h
    GS : GroupStructure (El G)
    GS = group-struct G
    HS : GroupStructure (El H)
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

    lemma : ∀ {i j k l} {C : Type i} {D : C → Type j} {E : C → Type k} 
      {F : Type l} {c₁ c₂ : C} {d₁ : D c₁} {d₂ : D c₂} {e₁ : E c₁} {e₂ : E c₂}
      (f : (c : C) → D c → E c → F) (p : c₁ == c₂) 
      → (d₁ == d₂ [ D ↓ p ]) → (e₁ == e₂ [ E ↓ p ])
      → (f c₁ d₁ e₁ == f c₂ d₂ e₂)
    lemma f idp idp idp = idp

module _ {i} {El : Type i} (GS : GroupStructure El) where
  
  private
    _⊙_ = comp GS

  group-inv-unique-l : (g h : El) → (g ⊙ h == ident GS) → inv GS h == g
  group-inv-unique-l g h p = 
    inv GS h              =⟨ ! (unitl GS (inv GS h)) ⟩
    ident GS ⊙ inv GS h   =⟨ ! p |in-ctx (λ w → w ⊙ inv GS h) ⟩
    (g ⊙ h) ⊙ inv GS h    =⟨ assoc GS g h (inv GS h) ⟩
    g ⊙ (h ⊙ inv GS h)    =⟨ invr GS h |in-ctx (λ w → g ⊙ w) ⟩
    g ⊙ (ident GS)        =⟨ unitr GS g ⟩
    g                     ∎
 
  group-inv-unique-r : (g h : El) → (g ⊙ h == ident GS) → inv GS g == h
  group-inv-unique-r g h p = 
    inv GS g              =⟨ ! (unitr GS (inv GS g)) ⟩
    inv GS g ⊙ ident GS   =⟨ ! p |in-ctx (λ w → inv GS g ⊙ w) ⟩
    inv GS g ⊙ (g ⊙ h)    =⟨ ! (assoc GS (inv GS g) g h) ⟩
    (inv GS g ⊙ g) ⊙ h    =⟨ invl GS g |in-ctx (λ w → w ⊙ h) ⟩
    ident GS ⊙ h          =⟨ unitl GS h ⟩
    h                     ∎

  group-inv-ident : inv GS (ident GS) == ident GS
  group-inv-ident = 
    group-inv-unique-l (ident GS) (ident GS) (unitl GS (ident GS))

