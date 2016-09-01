{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.types.Pointed

module lib.groups.Homomorphisms where

{-
Group homomorphisms.
-}

preserves-comp : ∀ {i j} {A : Type i} {B : Type j}
  (A-comp : A → A → A) (B-comp : B → B → B) (f : A → B)
  → Type (lmax i j)
preserves-comp Ac Bc f = ∀ a₁ a₂ → f (Ac a₁ a₂) == Bc (f a₁) (f a₂)

record GroupStructureHom {i j} {GEl : Type i} {HEl : Type j}
  (GS : GroupStructure GEl) (HS : GroupStructure HEl) : Type (lmax i j) where
  constructor group-structure-hom
  private
    module G = GroupStructure GS
    module H = GroupStructure HS
  field
    f : GEl → HEl
    pres-comp : preserves-comp G.comp H.comp f

  abstract
    pres-ident : f G.ident == H.ident
    pres-ident = H.cancel-l (f G.ident) $
      H.comp (f G.ident) (f G.ident)
        =⟨ ! (pres-comp G.ident G.ident) ⟩
      f (G.comp G.ident G.ident)
        =⟨ ap f (G.unit-l G.ident) ⟩
      f G.ident
        =⟨ ! (H.unit-r (f G.ident)) ⟩
      H.comp (f G.ident) H.ident =∎

    pres-inv : ∀ a → f (G.inv a) == H.inv (f a)
    pres-inv a =
      f (G.inv a)
        =⟨ ! (H.unit-r (f (G.inv a))) ⟩
      H.comp (f (G.inv a)) H.ident
        =⟨ ! (H.inv-r (f a))
           |in-ctx (λ w → H.comp (f (G.inv a)) w) ⟩
      H.comp (f (G.inv a)) (H.comp (f a) (H.inv (f a)))
        =⟨ ! (H.assoc (f (G.inv a)) (f a) (H.inv (f a))) ⟩
      H.comp (H.comp (f (G.inv a)) (f a)) (H.inv (f a))
        =⟨ ! (pres-comp (G.inv a) a) ∙ ap f (G.inv-l a) ∙ pres-ident
           |in-ctx (λ w → H.comp w (H.inv (f a))) ⟩
      H.comp H.ident (H.inv (f a))
        =⟨ H.unit-l (H.inv (f a)) ⟩
      H.inv (f a) =∎

  ⊙f : fst ((GEl , G.ident) ⊙→ (HEl , H.ident))
  ⊙f = f , pres-ident

infix 0 _→ᴳˢ_ -- [ˢ] for structures
_→ᴳˢ_ = GroupStructureHom

record GroupHom {i j} (G : Group i) (H : Group j) : Type (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
  field
    f : G.El → H.El
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)
  open GroupStructureHom {GS = G.group-struct} {HS = H.group-struct}
    record {f = f ; pres-comp = pres-comp} hiding (f ; pres-comp) public

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

→ᴳˢ-to-→ᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (Group.group-struct G →ᴳˢ Group.group-struct H) → (G →ᴳ H)
→ᴳˢ-to-→ᴳ (group-structure-hom f pres-comp) = group-hom f pres-comp

GroupStructureIso : ∀ {i j} {GEl : Type i} {HEl : Type j}
  (GS : GroupStructure GEl) (HS : GroupStructure HEl) → Type (lmax i j)
GroupStructureIso GS HS = Σ (GroupStructureHom GS HS) (λ φ → is-equiv (GroupStructureHom.f φ))

idhom : ∀ {i} (G : Group i) → (G →ᴳ G)
idhom G = group-hom (idf _) (λ _ _ → idp)

{- constant homomorphism -}
module _ where
  cst-hom : ∀ {i j} {G : Group i} {H : Group j} → (G →ᴳ H)
  cst-hom {H = H} = group-hom (cst (Group.ident H)) (λ _ _ → ! (Group.unit-l H _))

{- negation is a homomorphism in an abelian gruop -}
inv-hom : ∀ {i} (G : Group i) (G-abelian : is-abelian G) → GroupHom G G
inv-hom G G-abelian = group-hom
  (Group.inv G)
  (λ g₁ g₂ → Group.inv-comp G g₁ g₂ ∙ G-abelian (Group.inv G g₂) (Group.inv G g₁))

{- equality of homomorphisms -}
abstract
  group-hom= : ∀ {i j} {G : Group i} {H : Group j} {φ ψ : G →ᴳ H}
    → GroupHom.f φ == GroupHom.f ψ → φ == ψ
  group-hom= {H = H} p = ap (uncurry group-hom) $
    Subtype=-in (Π-level (λ _ → Π-level (λ _ → Group.El-level H _ _))) p

  group-hom=-↓ : ∀ {i j k} {A : Type i} {G : A → Group j} {H : A → Group k} {x y : A}
    {p : x == y} {φ : G x →ᴳ H x} {ψ : G y →ᴳ H y}
    → GroupHom.f φ == GroupHom.f ψ
      [ (λ a → Group.El (G a) → Group.El (H a)) ↓ p ]
    → φ == ψ [ (λ a → G a →ᴳ H a) ↓ p ]
  group-hom=-↓ {p = idp} = group-hom=

abstract
  GroupHom-level : ∀ {i j} {G : Group i} {H : Group j} → is-set (G →ᴳ H)
  GroupHom-level {H = H} = equiv-preserves-level
    (equiv (uncurry group-hom) (λ x → GroupHom.f x , GroupHom.pres-comp x)
           (λ _ → idp) (λ _ → idp))
    (Subtype-level (→-level (Group.El-level H))
                   (λ _ → Π-level λ _ → Π-level λ _ → Group.El-level H _ _))

→ᴳ-level = GroupHom-level

infixr 80 _∘ᴳ_

_∘ᴳ_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (H →ᴳ K) → (G →ᴳ H) → (G →ᴳ K)
ψ ∘ᴳ φ = group-hom
  (GroupHom.f ψ ∘ GroupHom.f φ)
  (λ x₁ x₂ → ap (GroupHom.f ψ) (GroupHom.pres-comp φ x₁ x₂)
           ∙ GroupHom.pres-comp ψ (GroupHom.f φ x₁) (GroupHom.f φ x₂))

{- algebraic properties -}

∘ᴳ-unit-r : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → φ ∘ᴳ idhom G == φ
∘ᴳ-unit-r φ = idp

∘ᴳ-unit-l : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → idhom H ∘ᴳ φ == φ
∘ᴳ-unit-l φ = group-hom= idp

∘ᴳ-assoc : ∀ {i j k l} {G : Group i} {H : Group j} {K : Group k} {L : Group l}
  (χ : K →ᴳ L) (ψ : H →ᴳ K) (φ : G →ᴳ H)
  → (χ ∘ᴳ ψ) ∘ᴳ φ == χ ∘ᴳ ψ ∘ᴳ φ
∘ᴳ-assoc χ ψ φ = group-hom= idp

pre∘-cst-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  (φ : H →ᴳ K)
  → φ ∘ᴳ cst-hom {G = G} {H = H} == cst-hom
pre∘-cst-hom φ = group-hom= $ λ= λ g → GroupHom.pres-ident φ

inv-hom-natural : ∀ {i j} {G : Group i} {H : Group j}
  (G-abelian : is-abelian G) (H-abelian : is-abelian H) (φ : G →ᴳ H)
  → φ ∘ᴳ inv-hom G G-abelian == inv-hom H H-abelian ∘ᴳ φ
inv-hom-natural _ _ φ = group-hom= $ λ= $ GroupHom.pres-inv φ

{-
Group isomorphisms.
-}

infix 30 _≃ᴳˢ_ -- [ˢ] for structures
_≃ᴳˢ_ = GroupStructureIso

GroupIso : ∀ {i j} (G : Group i) (H : Group j) → Type (lmax i j)
GroupIso G H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))

infix 30 _≃ᴳ_
_≃ᴳ_ = GroupIso

≃ᴳˢ-to-≃ᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (Group.group-struct G ≃ᴳˢ Group.group-struct H) → (G ≃ᴳ H)
≃ᴳˢ-to-≃ᴳ (φ , φ-is-equiv) = →ᴳˢ-to-→ᴳ φ , φ-is-equiv

≃-to-≃ᴳ : ∀ {i j} {G : Group i} {H : Group j} (e : Group.El G ≃ Group.El H)
  → preserves-comp (Group.comp G) (Group.comp H) (–> e) → G ≃ᴳ H
≃-to-≃ᴳ (f , f-is-equiv) pres-comp = group-hom f pres-comp , f-is-equiv

≃-to-≃ᴳˢ : ∀ {i j} {GEl : Type i} {HEl : Type j}
  {GS : GroupStructure GEl} {HS : GroupStructure HEl} (e : GEl ≃ HEl)
  → preserves-comp (GroupStructure.comp GS) (GroupStructure.comp HS) (–> e)
  → GS ≃ᴳˢ HS
≃-to-≃ᴳˢ (f , f-is-equiv) pres-comp = group-structure-hom f pres-comp , f-is-equiv

preserves-comp-inv : ∀ {i j} {A : Type i} {B : Type j}
  (A-comp : A → A → A) (B-comp : B → B → B) {f : A → B} (f-ie : is-equiv f)
  → preserves-comp A-comp B-comp f
  → preserves-comp B-comp A-comp (is-equiv.g f-ie)
preserves-comp-inv Ac Bc ie pc b₁ b₂ = let open is-equiv ie in
  ap2 (λ w₁ w₂ → g (Bc w₁ w₂)) (! (f-g b₁)) (! (f-g b₂))
  ∙ ! (ap g (pc (g b₁) (g b₂)))
  ∙ g-f (Ac (g b₁) (g b₂))

module GroupIso {i j} {G : Group i} {H : Group j} (iso : GroupIso G H) where

  f-hom : G →ᴳ H
  f-hom = fst iso

  open GroupHom {G = G} {H = H} f-hom public

  f-is-equiv : is-equiv f 
  f-is-equiv = snd iso

  open is-equiv f-is-equiv public

  f-equiv : Group.El G ≃ Group.El H
  f-equiv = f , f-is-equiv

  g-hom : H →ᴳ G
  g-hom = group-hom g (preserves-comp-inv (Group.comp G) (Group.comp H) f-is-equiv pres-comp)

idiso : ∀ {i} (G : Group i) → (G ≃ᴳ G)
idiso G = idhom G , idf-is-equiv _

≃ᴳ-over-= : ∀ {i j} {A : Type i} (B : A → Group j) {a₁ a₂ : A} (p : a₁ == a₂)
  → B a₁ ≃ᴳ B a₂
≃ᴳ-over-= B idp = idiso _

{- equality of isomomorphisms -}
abstract
  group-hom=-to-iso= : ∀ {i j} {G : Group i} {H : Group j} {φ ψ : G ≃ᴳ H}
    → GroupIso.f-hom φ == GroupIso.f-hom ψ → φ == ψ
  group-hom=-to-iso= p = Subtype=-in (is-equiv-is-prop _) p

  group-iso= : ∀ {i j} {G : Group i} {H : Group j} {φ ψ : G ≃ᴳ H}
    → GroupIso.f φ == GroupIso.f ψ → φ == ψ
  group-iso= {H = H} p = group-hom=-to-iso= $ group-hom= p

infixr 80 _∘eᴳ_

_∘eᴳ_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → H ≃ᴳ K → G ≃ᴳ H → G ≃ᴳ K
(φ₂ , ie₂) ∘eᴳ (φ₁ , ie₁) = (φ₂ ∘ᴳ φ₁ , ie₂ ∘ise ie₁)

infixr 10 _≃ᴳ⟨_⟩_
infix  15 _≃ᴳ∎

_≃ᴳ⟨_⟩_ : ∀ {i j k} (G : Group i) {H : Group j} {K : Group k}
  → G ≃ᴳ H → H ≃ᴳ K → G ≃ᴳ K
G ≃ᴳ⟨ e₁ ⟩ e₂ = e₂ ∘eᴳ e₁

_≃ᴳ∎ : ∀ {i} (G : Group i) → (G ≃ᴳ G)
_≃ᴳ∎ = idiso

infixl 120 _⁻¹ᴳ

_⁻¹ᴳ : ∀ {i j} {G : Group i} {H : Group j} → G ≃ᴳ H → H ≃ᴳ G
_⁻¹ᴳ {G = G} {H = H} (φ , ie) =
  group-hom
    (is-equiv.g ie)
    (preserves-comp-inv (Group.comp G) (Group.comp H) ie (GroupHom.pres-comp φ)) ,
  is-equiv-inv ie

–>ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (G ≃ᴳ H) → (G →ᴳ H)
–>ᴳ = GroupIso.f-hom

<–ᴳ : ∀ {i j} {G : Group i} {H : Group j} → (G ≃ᴳ H) → (H →ᴳ G)
<–ᴳ = GroupIso.g-hom

module _ {i} {G H : Group i} (iso : GroupIso G H) where
  private
    module G = Group G
    module H = Group H
    open module φ = GroupIso {G = G} {H = H} iso
  El= = ua f-equiv

  private
    ap3-lemma : ∀ {i j k l} {C : Type i} {D : C → Type j} {E : C → Type k}
      {F : Type l} {c₁ c₂ : C} {d₁ : D c₁} {d₂ : D c₂} {e₁ : E c₁} {e₂ : E c₂}
      (f : (c : C) → D c → E c → F) (p : c₁ == c₂)
      → (d₁ == d₂ [ D ↓ p ]) → (e₁ == e₂ [ E ↓ p ])
      → (f c₁ d₁ e₁ == f c₂ d₂ e₂)
    ap3-lemma f idp idp idp = idp

    ap3-lemma-El : ∀ {i} {G H : Group i}
      (p : Group.El G == Group.El H)
      (q : Group.El-level G == Group.El-level H [ _ ↓ p ])
      (r : Group.group-struct G == Group.group-struct H [ _ ↓ p ])
      → ap Group.El (ap3-lemma group p q r) == p
    ap3-lemma-El idp idp idp = idp

  {- a homomorphism which is an equivalence gives a path between groups -}
  abstract
    uaᴳ : G == H
    uaᴳ =
      ap3-lemma group
        El=
        (prop-has-all-paths-↓ has-level-is-prop)
        (↓-group-structure= (G.El-level) El= ident= inv= comp=)
      where
      ident= : G.ident == H.ident [ (λ C → C) ↓ El= ]
      ident= = ↓-idf-ua-in _ pres-ident

      inv= : G.inv == H.inv [ (λ C → C → C) ↓ El= ]
      inv= =
        ↓-→-from-transp $ λ= λ a →
          transport (λ C → C) El= (G.inv a)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          f (G.inv a)
            =⟨ pres-inv a ⟩
          H.inv (f a)
            =⟨ ap H.inv (! (to-transp (↓-idf-ua-in _ idp))) ⟩
          H.inv (transport (λ C → C) El= a) =∎

      comp=' : (a : G.El)
        → G.comp a == H.comp (f a) [ (λ C → C → C) ↓ El= ]
      comp=' a =
        ↓-→-from-transp $ λ= λ b →
          transport (λ C → C) El= (G.comp a b)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          f (G.comp a b)
            =⟨ pres-comp a b ⟩
          H.comp (f a) (f b)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp))
               |in-ctx (λ w → H.comp (f a) w) ⟩
          H.comp (f a) (transport (λ C → C) El= b) =∎

      comp= : G.comp == H.comp [ (λ C → C → C → C) ↓ El= ]
      comp= =
        ↓-→-from-transp $ λ= λ a →
          transport (λ C → C → C) El= (G.comp a)
            =⟨ to-transp (comp=' a) ⟩
          H.comp (f a)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → H.comp w) ⟩
          H.comp (transport (λ C → C) El= a) =∎

    -- XXX This stretches the naming convention a little bit.
    El=-β : ap Group.El uaᴳ == El=
    El=-β = ap3-lemma-El El= _ _

{- homomorphism from equality of groups -}
coeᴳ : ∀ {i} {G H : Group i} → G == H → (G →ᴳ H)
coeᴳ idp = idhom _

coe!ᴳ : ∀ {i} {G H : Group i} → G == H → (H →ᴳ G)
coe!ᴳ idp = idhom _

coeᴳ-fun : ∀ {i} {G H : Group i} (p : G == H)
  → GroupHom.f (coeᴳ p) == coe (ap Group.El p)
coeᴳ-fun idp = idp

coe!ᴳ-fun : ∀ {i} {G H : Group i} (p : G == H)
  → GroupHom.f (coe!ᴳ p) == coe! (ap Group.El p)
coe!ᴳ-fun idp = idp

coeᴳ-β : ∀ {i} {G H : Group i} (iso : G ≃ᴳ H)
  → coeᴳ (uaᴳ iso) == GroupIso.f-hom iso
coeᴳ-β iso = group-hom= $
  coeᴳ-fun (uaᴳ iso)
  ∙ ap coe (El=-β iso)
  ∙ λ= (coe-β (GroupIso.f-equiv iso))

-- TODO move this to PropSubgroup?
{- homomorphism with kernel zero is injective -}
module _ {i j} {G : Group i} {H : Group j} (φ : (G →ᴳ H)) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom {G = G} {H = H} φ

  zero-ker-inj : ((g : G.El) → φ.f g == H.ident → g == G.ident)
    → ((g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
  zero-ker-inj f g₁ g₂ p =
    ! (G.inv-inv g₁) ∙ G.inv-unique-r (G.inv g₁) g₂ (f _ $
      φ.f (G.comp (G.inv g₁) g₂)
        =⟨ φ.pres-comp (G.inv g₁) g₂ ⟩
      H.comp (φ.f (G.inv g₁)) (φ.f g₂)
        =⟨ φ.pres-inv g₁ |in-ctx (λ w → H.comp w (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₁)) (φ.f g₂)
        =⟨ p |in-ctx (λ w → H.comp (H.inv w) (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₂)) (φ.f g₂)
        =⟨ H.inv-l (φ.f g₂) ⟩
      H.ident =∎)

{- a surjective and injective homomorphism is an isomorphism -}
module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom {G = G} {H = H} φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Trunc -1 (Σ G.El (λ g → φ.f g == h))) where

    private
      image-prop : (h : H.El) → is-prop (Σ G.El (λ g → φ.f g == h))
      image-prop h = all-paths-is-prop $ λ {(g₁ , p₁) (g₂ , p₂) →
        pair= (inj g₁ g₂ (p₁ ∙ ! p₂)) (prop-has-all-paths-↓ (H.El-level _ _))}

    surj-inj-is-equiv : is-equiv φ.f
    surj-inj-is-equiv = contr-map-is-equiv
      (λ h → let (g₁ , p₁) = Trunc-rec (image-prop h) (idf _) (surj h) in
        ((g₁ , p₁) , (λ {(g₂ , p₂) →
          pair= (inj g₁ g₂ (p₁ ∙ ! p₂))
                (prop-has-all-paths-↓ (H.El-level _ _))})))

    surj-inj-iso : G ≃ᴳ H
    surj-inj-iso = φ , surj-inj-is-equiv

module _ {i} {G H : Group i} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom {G = G} {H = H} φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Trunc -1 (Σ G.El (λ g → φ.f g == h))) where

    surj-inj-path : G == H
    surj-inj-path = uaᴳ (surj-inj-iso φ inj surj)

{- two homomorphisms into an abelian group can be composed with
 - the group operation -}
module _ {i} {G H : Group i} (H-abelian : is-abelian H)
  (φ ψ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom {G = G} {H = H} φ
    module ψ = GroupHom {G = G} {H = H} ψ

  hom-comp : G →ᴳ H
  hom-comp = group-hom
    (λ g → H.comp (φ.f g) (ψ.f g))
    (λ g₁ g₂ →
      H.comp (φ.f (G.comp g₁ g₂)) (ψ.f (G.comp g₁ g₂))
        =⟨ ap2 H.comp (φ.pres-comp g₁ g₂) (ψ.pres-comp g₁ g₂) ⟩
      H.comp (H.comp (φ.f g₁) (φ.f g₂)) (H.comp (ψ.f g₁) (ψ.f g₂))
        =⟨ lemma (φ.f g₁) (φ.f g₂) (ψ.f g₁) (ψ.f g₂) ⟩
      H.comp (H.comp (φ.f g₁) (ψ.f g₁)) (H.comp (φ.f g₂) (ψ.f g₂)) =∎)

    where
    lemma : (h₁ h₂ h₃ h₄ : H.El) →
      H.comp (H.comp h₁ h₂) (H.comp h₃ h₄)
      == H.comp (H.comp h₁ h₃) (H.comp h₂ h₄)
    lemma h₁ h₂ h₃ h₄ =
      (h₁ □ h₂) □ (h₃ □ h₄)
         =⟨ H.assoc h₁ h₂ (h₃ □ h₄) ⟩
       h₁ □ (h₂ □ (h₃ □ h₄))
         =⟨ H-abelian h₃ h₄ |in-ctx (λ w → h₁ □ (h₂ □ w)) ⟩
       h₁ □ (h₂ □ (h₄ □ h₃))
         =⟨ ! (H.assoc h₂ h₄ h₃) |in-ctx (λ w → h₁ □ w) ⟩
       h₁ □ ((h₂ □ h₄) □ h₃)
         =⟨ H-abelian (h₂ □ h₄) h₃ |in-ctx (λ w → h₁ □ w) ⟩
       h₁ □ (h₃ □ (h₂ □ h₄))
         =⟨ ! (H.assoc h₁ h₃ (h₂ □ h₄)) ⟩
       (h₁ □ h₃) □ (h₂ □ h₄) =∎
       where
        infix 80 _□_
        _□_ = H.comp

-- Isomorphisms preserve abelianess.
module _ {i} {G H : Group i} (iso : G ≃ᴳ H) (G-abelian : is-abelian G) where
  private
    module G = Group G
    module H = Group H
    open GroupIso iso

  abstract
    iso-preserves-abelian : is-abelian H
    iso-preserves-abelian h₁ h₂ =
      H.comp h₁ h₂
        =⟨ ap2 H.comp (! $ f-g h₁) (! $ f-g h₂) ⟩
      H.comp (f (g h₁)) (f (g h₂))
        =⟨ ! $ pres-comp (g h₁) (g h₂) ⟩
      f (G.comp (g h₁) (g h₂))
        =⟨ G-abelian (g h₁) (g h₂) |in-ctx f ⟩
      f (G.comp (g h₂) (g h₁))
        =⟨ pres-comp (g h₂) (g h₁) ⟩
      H.comp (f (g h₂)) (f (g h₁))
        =⟨ ap2 H.comp (f-g h₂) (f-g h₁) ⟩
      H.comp h₂ h₁
        =∎
