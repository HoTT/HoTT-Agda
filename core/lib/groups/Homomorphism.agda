{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.Function2
open import lib.NType2
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Subtype
open import lib.types.Truncation
open import lib.groups.SubgroupProp

module lib.groups.Homomorphism where

{-
Group homomorphisms.
-}

preserves-comp : ∀ {i j} {A : Type i} {B : Type j}
  (A-comp : A → A → A) (B-comp : B → B → B) (f : A → B)
  → Type (lmax i j)
preserves-comp Ac Bc f = ∀ a₁ a₂ → f (Ac a₁ a₂) == Bc (f a₁) (f a₂)

preserves-comp-is-prop : ∀ {i j} {A : Type i} {B : Type j}
  (pB : is-set B) (A-comp : A → A → A) (B-comp : B → B → B)
  → (f : A → B) → is-prop (preserves-comp A-comp B-comp f)
preserves-comp-is-prop pB Ac Bc f = Π-is-prop λ _ → Π-is-prop λ _ → pB _ _

preserves-comp-prop : ∀ {i j} {A : Type i} {B : Type j}
  (pB : is-set B) (A-comp : A → A → A) (B-comp : B → B → B)
  → SubtypeProp (A → B) (lmax i j)
preserves-comp-prop pB Ac Bc =
  preserves-comp Ac Bc , preserves-comp-is-prop pB Ac Bc

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

  ⊙f : (GEl , G.ident) ⊙→ (HEl , H.ident)
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

idhom : ∀ {i} (G : Group i) → (G →ᴳ G)
idhom G = group-hom (idf _) (λ _ _ → idp)

{- constant (zero) homomorphism -}
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
  group-hom= {G = G} {H = H} p = ap (uncurry group-hom) $
    Subtype=-out (preserves-comp-prop (Group.El-level H) (Group.comp G) (Group.comp H)) p

  group-hom=-↓ : ∀ {i j k} {A : Type i} {G : A → Group j} {H : A → Group k} {x y : A}
    {p : x == y} {φ : G x →ᴳ H x} {ψ : G y →ᴳ H y}
    → GroupHom.f φ == GroupHom.f ψ
      [ (λ a → Group.El (G a) → Group.El (H a)) ↓ p ]
    → φ == ψ [ (λ a → G a →ᴳ H a) ↓ p ]
  group-hom=-↓ {p = idp} = group-hom=

abstract
  GroupHom-level : ∀ {i j} {G : Group i} {H : Group j} → is-set (G →ᴳ H)
  GroupHom-level {G = G} {H = H} = equiv-preserves-level
    (equiv (uncurry group-hom) (λ x → GroupHom.f x , GroupHom.pres-comp x)
           (λ _ → idp) (λ _ → idp))
    (Subtype-level
      (preserves-comp-prop (Group.El-level H) (Group.comp G) (Group.comp H))
      (→-level (Group.El-is-set H)))

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

is-injᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (G →ᴳ H) → Type (lmax i j)
is-injᴳ hom = is-inj (GroupHom.f hom)

is-surjᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (G →ᴳ H) → Type (lmax i j)
is-surjᴳ hom = is-surj (GroupHom.f hom)

{- subgroups -}

infix 80 _∘subᴳ_
_∘subᴳ_ : ∀ {i j k} {G : Group i} {H : Group j}
  → SubgroupProp H k → (G →ᴳ H) → SubgroupProp G k
_∘subᴳ_ {G = G} {H} P φ = record {
  prop = P.prop ∘ φ.f;
  level = P.level ∘ φ.f;
  ident = transport! P.prop φ.pres-ident P.ident;
  comp-inv-r = λ {g₁} {g₂} pφg₁ pφg₂ → transport! P.prop
    (φ.pres-comp g₁ (G.inv g₂) ∙ ap (H.comp (φ.f g₁)) (φ.pres-inv g₂))
    (P.comp-inv-r pφg₁ pφg₂)}
  where module G = Group G
        module H = Group H
        module P = SubgroupProp P
        module φ = GroupHom φ

infix 80 _∘nsubᴳ_
_∘nsubᴳ_ : ∀ {i j k} {G : Group i} {H : Group j}
  → NormalSubgroupProp H k → (G →ᴳ H) → NormalSubgroupProp G k
_∘nsubᴳ_ {G = G} {H} P φ = P.subgrp-prop ∘subᴳ φ , P-φ-is-normal
  where module G = Group G
        module H = Group H
        module P = NormalSubgroupProp P
        module φ = GroupHom φ
        abstract
          P-φ-is-normal : is-normal (P.subgrp-prop ∘subᴳ φ)
          P-φ-is-normal g₁ {g₂} pφg₂ = transport! P.prop
            ( φ.pres-comp (G.comp g₁ g₂) (G.inv g₁)
            ∙ ap2 H.comp (φ.pres-comp g₁ g₂) (φ.pres-inv g₁))
            (P.conj (φ.f g₁) pφg₂)

{- kernels and images -}

module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  ker-propᴳ : SubgroupProp G j
  ker-propᴳ = record {
    prop = λ g → φ.f g == H.ident;
    level = λ g → H.El-level _ _;
    ident = φ.pres-ident;
    comp-inv-r = λ {g₁} {g₂} p₁ p₂
      → φ.pres-comp g₁ (G.inv g₂)
      ∙ ap2 H.comp p₁ ( φ.pres-inv g₂
                      ∙ ap H.inv p₂ ∙ H.inv-ident)
      ∙ H.unit-l H.ident }

  ker-is-normal : is-normal ker-propᴳ
  ker-is-normal g₁ {g₂} pg₂ =
      φ.pres-comp (G.comp g₁ g₂) (G.inv g₁)
    ∙ ap2 H.comp (φ.pres-comp g₁ g₂ ∙ ap (H.comp (φ.f g₁)) pg₂ ∙ H.unit-r (φ.f g₁))
                 (φ.pres-inv g₁)
    ∙ H.inv-r (φ.f g₁)

  im-propᴳ : SubgroupProp H (lmax i j)
  im-propᴳ = record {
    prop = λ h → Trunc -1 (hfiber φ.f h);
    level = λ h → Trunc-level;
    ident = [ G.ident , φ.pres-ident ];
    comp-inv-r = Trunc-fmap2 (λ {(g₁ , p₁) (g₂ , p₂)
      → G.comp g₁ (G.inv g₂)
      , φ.pres-comp g₁ (G.inv g₂)
      ∙ ap2 H.comp p₁ (φ.pres-inv g₂ ∙ ap H.inv p₂)})}

  has-trivial-kerᴳ : Type (lmax i j)
  has-trivial-kerᴳ = ker-propᴳ ⊆ᴳ trivial-propᴳ G

  -- any homomorphism with trivial kernel is injective
  has-trivial-ker-is-injᴳ : has-trivial-kerᴳ → is-injᴳ φ
  has-trivial-ker-is-injᴳ tk g₁ g₂ p =
    ! (G.inv-inv g₁) ∙ G.inv-unique-r (G.inv g₁) g₂ (tk _ $
      φ.f (G.comp (G.inv g₁) g₂)
        =⟨ φ.pres-comp (G.inv g₁) g₂ ⟩
      H.comp (φ.f (G.inv g₁)) (φ.f g₂)
        =⟨ φ.pres-inv g₁ |in-ctx (λ w → H.comp w (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₁)) (φ.f g₂)
        =⟨ p |in-ctx (λ w → H.comp (H.inv w) (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₂)) (φ.f g₂)
        =⟨ H.inv-l (φ.f g₂) ⟩
      H.ident =∎)


{- exactness -}

module _ {i j k} {G : Group i} {H : Group j} {K : Group k}
  (φ : G →ᴳ H) (ψ : H →ᴳ K) where

  private
    module G = Group G
    module H = Group H
    module K = Group K
    module φ = GroupHom φ
    module ψ = GroupHom ψ

  record is-exact : Type (lmax k (lmax j i)) where
    field
      im-sub-ker : im-propᴳ φ ⊆ᴳ ker-propᴳ ψ
      ker-sub-im : ker-propᴳ ψ ⊆ᴳ  im-propᴳ φ

  open is-exact public

  {- an equivalent version of is-exact-ktoi  -}
  im-sub-ker-in : is-fullᴳ (ker-propᴳ (ψ ∘ᴳ φ)) → im-propᴳ φ ⊆ᴳ ker-propᴳ ψ
  im-sub-ker-in r h = Trunc-rec (K.El-level _ _) (λ {(g , p) → ap ψ.f (! p) ∙ r g})

  im-sub-ker-out : im-propᴳ φ ⊆ᴳ ker-propᴳ ψ → is-fullᴳ (ker-propᴳ (ψ ∘ᴳ φ))
  im-sub-ker-out s g = s (φ.f g) [ g , idp ]

{- two homomorphisms into an abelian group can be composed with
 - the group operation -}
module _ {i} {G H : Group i} (H-abelian : is-abelian H)
  (φ ψ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ
    module ψ = GroupHom ψ

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
