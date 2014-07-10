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

record Group i : Type (lsucc i) where
  constructor group
  field
    El : Type i
    El-level : has-level ⟨0⟩ El
    group-struct : GroupStructure El
  open GroupStructure group-struct public

  Ptd-El : Σ (Type i) (λ A → A)
  Ptd-El = (El , ident)

Group₀ : Type (lsucc lzero)
Group₀ = Group lzero

is-abelian : ∀ {i} → Group i → Type i
is-abelian G = (a b : Group.El G) → Group.comp G a b == Group.comp G b a

record GroupHom {i j} (G : Group i) (H : Group j)
  : Type (lsucc (lmax i j)) where
  constructor group-hom

  field
    f : Group.El G → Group.El H
    pres-ident : f (Group.ident G) == Group.ident H
    pres-comp  : ∀ g1 g2 → f (Group.comp G g1 g2) == Group.comp H (f g1) (f g2)

  ptd-f : Σ (Group.El G → Group.El H)
            (λ f → f (Group.ident G) == Group.ident H)
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

abstract
  hom= : ∀ {i j} {G : Group i} {H : Group j} (h k : GroupHom G H)
    → GroupHom.f h == GroupHom.f k → h == k
  hom= {H = H} (group-hom f f-id f-comp) (group-hom g g-id g-comp) p =
    ap (λ {(h , (h-id , h-comp)) → group-hom h h-id h-comp})
       (pair= p
         (prop-has-all-paths-↓
           (×-level (Group.El-level H _ _)
                    (Π-level (λ _ → Π-level (λ _ → Group.El-level H _ _))))))

module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  grouphom-pres-inv : (a : G.El) → φ.f (G.inv a) == H.inv (φ.f a)
  grouphom-pres-inv a =
    φ.f (G.inv a)
      =⟨ ! (H.unitr (φ.f (G.inv a))) ⟩
    H.comp (φ.f (G.inv a)) H.ident
      =⟨ ! (H.invr (φ.f a)) |in-ctx (λ w → H.comp (φ.f (G.inv a)) w) ⟩
    H.comp (φ.f (G.inv a)) (H.comp (φ.f a) (H.inv (φ.f a)))
      =⟨ ! (H.assoc (φ.f (G.inv a)) (φ.f a) (H.inv (φ.f a))) ⟩
    H.comp (H.comp (φ.f (G.inv a)) (φ.f a)) (H.inv (φ.f a))
      =⟨ lemma |in-ctx (λ w → H.comp w (H.inv (φ.f a))) ⟩
    H.comp H.ident (H.inv (φ.f a))
      =⟨ H.unitl (H.inv (φ.f a)) ⟩
    H.inv (φ.f a) ∎
    where
    lemma : H.comp (φ.f (G.inv a)) (φ.f a) == H.ident
    lemma = ! (φ.pres-comp (G.inv a) a) ∙ ap φ.f (G.invl a) ∙ φ.pres-ident

module _ where
  open GroupStructure

  abstract
    group-structure= : ∀ {i} {A : Type i} (pA : has-level ⟨0⟩ A)
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
      (A-level : has-level ⟨0⟩ A)
      {GS : GroupStructure A} {HS : GroupStructure B} (p : A == B)
      → (ident GS == ident HS [ (λ C → C) ↓ p ])
      → (inv GS == inv HS [ (λ C → C → C) ↓ p ])
      → (comp GS == comp HS [ (λ C → C → C → C) ↓ p ])
      → GS == HS [ GroupStructure ↓ p ]
    ↓-group-structure= A-level idp = group-structure= A-level

module _ {i} {G H : Group i} (φ : GroupHom G H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  abstract
    group-iso : is-equiv (GroupHom.f φ) → G == H
    group-iso e =
      lemma group
        (ua (φ.f , e))
        (prop-has-all-paths-↓ has-level-is-prop)
        (↓-group-structure= (G.El-level) (ua (φ.f , e)) ident= inv= comp=)
      where
      ident= : G.ident == H.ident [ (λ C → C) ↓ ua (φ.f , e) ]
      ident= = ↓-idf-ua-in _ φ.pres-ident

      inv= : G.inv == H.inv [ (λ C → C → C) ↓ ua (φ.f , e) ]
      inv= =
        ↓-→-from-transp $ λ= $ λ a →
          transport (λ C → C) (ua (φ.f , e)) (G.inv a)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          φ.f (G.inv a)
            =⟨ grouphom-pres-inv φ a ⟩
          H.inv (φ.f a)
            =⟨ ap H.inv (! (to-transp (↓-idf-ua-in _ idp))) ⟩
          H.inv (transport (λ C → C) (ua (φ.f , e)) a) ∎

      comp=' : (a : G.El)
        → G.comp a == H.comp (φ.f a) [ (λ C → C → C) ↓ ua (φ.f , e) ]
      comp=' a =
        ↓-→-from-transp $ λ= $ λ b →
          transport (λ C → C) (ua (φ.f , e)) (G.comp a b)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          φ.f (G.comp a b)
            =⟨ φ.pres-comp a b ⟩
          H.comp (φ.f a) (φ.f b)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → H.comp (φ.f a) w) ⟩
          H.comp (φ.f a) (transport (λ C → C) (ua (φ.f , e)) b) ∎

      comp= : G.comp == H.comp [ (λ C → C → C → C) ↓ ua (φ.f , e) ]
      comp= =
        ↓-→-from-transp $ λ= $ λ a →
          transport (λ C → C → C) (ua (φ.f , e)) (G.comp a)
            =⟨ to-transp (comp=' a) ⟩
          H.comp (φ.f a)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → H.comp w) ⟩
          H.comp (transport (λ C → C) (ua (φ.f , e)) a) ∎

      lemma : ∀ {i j k l} {C : Type i} {D : C → Type j} {E : C → Type k}
        {F : Type l} {c₁ c₂ : C} {d₁ : D c₁} {d₂ : D c₂} {e₁ : E c₁} {e₂ : E c₂}
        (f : (c : C) → D c → E c → F) (p : c₁ == c₂)
        → (d₁ == d₂ [ D ↓ p ]) → (e₁ == e₂ [ E ↓ p ])
        → (f c₁ d₁ e₁ == f c₂ d₂ e₂)
      lemma f idp idp idp = idp

module _ {i} (G : Group i) where
  private
    open Group G
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

  inv-inv : (g : El) → inv (inv g) == g
  inv-inv g = group-inv-unique-r (inv g) g (invl g)
