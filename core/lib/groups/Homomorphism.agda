{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.Function2
open import lib.NType2
open import lib.types.Group
open import lib.types.Pi
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

    pres-inv : ∀ g → f (G.inv g) == H.inv (f g)
    pres-inv g = ! $ H.inv-unique-l _ _ $
      H.comp (f (G.inv g)) (f g)
        =⟨ ! (pres-comp (G.inv g) g) ⟩
      f (G.comp (G.inv g) g)
        =⟨ ap f (G.inv-l g) ⟩
      f G.ident
        =⟨ pres-ident ⟩
      H.ident
        =∎

    -- pres-exp TODO

    pres-conj : ∀ g h → f (G.conj g h) == H.conj (f g) (f h)
    pres-conj g h = pres-comp (G.comp g h) (G.inv g) ∙ ap2 H.comp (pres-comp g h) (pres-inv g)

    pres-diff : ∀ g h → f (G.diff g h) == H.diff (f g) (f h)
    pres-diff g h = pres-comp g (G.inv h) ∙ ap (H.comp (f g)) (pres-inv h)

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
inv-hom : ∀ {i} (G : AbGroup i) → GroupHom (AbGroup.grp G) (AbGroup.grp G)
inv-hom G = group-hom G.inv inv-pres-comp where
  module G = AbGroup G
  abstract
    inv-pres-comp : (g₁ g₂ : G.El) → G.inv (G.comp g₁ g₂) == G.comp (G.inv g₁) (G.inv g₂)
    inv-pres-comp g₁ g₂ = G.inv-comp g₁ g₂ ∙ G.comm (G.inv g₂) (G.inv g₁)

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

{- TODO Use [comm-sqrᴳ] -}
inv-hom-natural : ∀ {i j} (G : AbGroup i) (H : AbGroup j)
  (φ : AbGroup.grp G →ᴳ AbGroup.grp H)
  → φ ∘ᴳ inv-hom G == inv-hom H ∘ᴳ φ
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
_∘subᴳ_ {k = k} {G = G} P φ = record {M} where
  module G = Group G
  module P = SubgroupProp P
  module φ = GroupHom φ
  module M where
    prop : G.El → Type k
    prop = P.prop ∘ φ.f

    level : ∀ g → is-prop (prop g)
    level = P.level ∘ φ.f

    abstract
      ident : prop G.ident
      ident = transport! P.prop φ.pres-ident P.ident

      diff : {g₁ g₂ : G.El} → prop g₁ → prop g₂ → prop (G.diff g₁ g₂)
      diff {g₁} {g₂} pφg₁ pφg₂ = transport! P.prop
        (φ.pres-diff g₁ g₂)
        (P.diff pφg₁ pφg₂)

infix 80 _∘nsubᴳ_
_∘nsubᴳ_ : ∀ {i j k} {G : Group i} {H : Group j}
  → NormalSubgroupProp H k → (G →ᴳ H) → NormalSubgroupProp G k
_∘nsubᴳ_ {G = G} {H} P φ = P.propᴳ ∘subᴳ φ , P-φ-is-normal
  where module P = NormalSubgroupProp P
        module φ = GroupHom φ
        abstract
          P-φ-is-normal : is-normal (P.propᴳ ∘subᴳ φ)
          P-φ-is-normal g₁ {g₂} pφg₂ = transport! P.prop
            (φ.pres-conj g₁ g₂)
            (P.conj (φ.f g₁) pφg₂)

{- kernels and images -}

module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  ker-propᴳ : SubgroupProp G j
  ker-propᴳ = record {M} where
    module M where
      prop : G.El → Type j
      prop g = φ.f g == H.ident
      abstract
        level : (g : G.El) → is-prop (prop g)
        level g = H.El-level _ _

        ident : prop G.ident
        ident = φ.pres-ident

        diff : {g₁ g₂ : G.El} → prop g₁ → prop g₂ → prop (G.diff g₁ g₂)
        diff {g₁} {g₂} p₁ p₂ = φ.pres-diff g₁ g₂ ∙ ap2 H.diff p₁ p₂ ∙ H.inv-r H.ident

  -- 'n' for 'normal'
  ker-npropᴳ : NormalSubgroupProp G j
  ker-npropᴳ = ker-propᴳ , ker-is-normal where
    abstract
      ker-is-normal : is-normal ker-propᴳ
      ker-is-normal g₁ {g₂} pg₂ =
          φ.pres-conj g₁ g₂
        ∙ ap (H.conj (φ.f g₁)) pg₂
        ∙ H.conj-ident-r (φ.f g₁)

  im-propᴳ : SubgroupProp H (lmax i j)
  im-propᴳ = record {M} where
    module M where
      prop : H.El → Type (lmax i j)
      prop h = Trunc -1 (hfiber φ.f h)

      level : (h : H.El) → is-prop (prop h)
      level h = Trunc-level

      abstract
        ident : prop H.ident
        ident = [ G.ident , φ.pres-ident ]

        diff : {h₁ h₂ : H.El} → prop h₁ → prop h₂ → prop (H.diff h₁ h₂)
        diff = Trunc-fmap2 λ {(g₁ , p₁) (g₂ , p₂)
          → G.diff g₁ g₂ , φ.pres-diff g₁ g₂ ∙ ap2 H.diff p₁ p₂}

  im-npropᴳ : is-abelian H → NormalSubgroupProp H (lmax i j)
  im-npropᴳ H-is-abelian = sub-abelian-normal H-is-abelian im-propᴳ

  has-trivial-kerᴳ : Type (lmax i j)
  has-trivial-kerᴳ = is-trivial-propᴳ ker-propᴳ

  abstract
    -- any homomorphism with trivial kernel is injective
    has-trivial-ker-is-injᴳ : has-trivial-kerᴳ → is-injᴳ φ
    has-trivial-ker-is-injᴳ tk g₁ g₂ p =
      G.zero-diff-same g₁ g₂ $ tk (G.diff g₁ g₂) $
        φ.pres-diff g₁ g₂ ∙ ap (λ h → H.diff h (φ.f g₂)) p ∙ H.inv-r (φ.f g₂)


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

  abstract
    {- an equivalent version of is-exact-ktoi  -}
    im-sub-ker-in : is-fullᴳ (ker-propᴳ (ψ ∘ᴳ φ)) → im-propᴳ φ ⊆ᴳ ker-propᴳ ψ
    im-sub-ker-in r h = Trunc-rec (K.El-level _ _) (λ {(g , p) → ap ψ.f (! p) ∙ r g})

    im-sub-ker-out : im-propᴳ φ ⊆ᴳ ker-propᴳ ψ → is-fullᴳ (ker-propᴳ (ψ ∘ᴳ φ))
    im-sub-ker-out s g = s (φ.f g) [ g , idp ]

{- homomorphisms into an abelian group can be composed with
 - the group operation and form a group -}
module _ {i j} (G : Group i) (H : AbGroup j)
  where

  private
    module G = Group G
    module H = AbGroup H

    hom-comp : (G →ᴳ H.grp) → (G →ᴳ H.grp) → (G →ᴳ H.grp)
    hom-comp φ ψ = group-hom (λ g → H.comp (φ.f g) (ψ.f g)) hom-comp-pres-comp where
      module φ = GroupHom φ
      module ψ = GroupHom ψ
      abstract
        hom-comp-pres-comp : ∀ g₁ g₂
          →  H.comp (φ.f (G.comp g₁ g₂)) (ψ.f (G.comp g₁ g₂))
          == H.comp (H.comp (φ.f g₁) (ψ.f g₁)) (H.comp (φ.f g₂) (ψ.f g₂))
        hom-comp-pres-comp g₁ g₂ =
          H.comp (φ.f (G.comp g₁ g₂)) (ψ.f (G.comp g₁ g₂))
            =⟨ ap2 H.comp (φ.pres-comp g₁ g₂) (ψ.pres-comp g₁ g₂) ⟩
          H.comp (H.comp (φ.f g₁) (φ.f g₂)) (H.comp (ψ.f g₁) (ψ.f g₂))
            =⟨ H.interchange (φ.f g₁) (φ.f g₂) (ψ.f g₁) (ψ.f g₂) ⟩
          H.comp (H.comp (φ.f g₁) (ψ.f g₁)) (H.comp (φ.f g₂) (ψ.f g₂)) =∎

  hom-group-structure : GroupStructure (G →ᴳ H.grp)
  hom-group-structure = record {M} where
    module M where
      ident : G →ᴳ H.grp
      ident = cst-hom

      comp : (G →ᴳ H.grp) → (G →ᴳ H.grp) → (G →ᴳ H.grp)
      comp = hom-comp

      inv : (G →ᴳ H.grp) → (G →ᴳ H.grp)
      inv φ = inv-hom H ∘ᴳ φ

      abstract
        unit-l : ∀ φ → comp ident φ == φ
        unit-l φ = group-hom= $ λ= λ _ → H.unit-l _

        unit-r : ∀ φ → comp φ ident == φ
        unit-r φ = group-hom= $ λ= λ _ → H.unit-r _

        assoc : ∀ φ ψ ξ → comp (comp φ ψ) ξ == comp φ (comp ψ ξ)
        assoc φ ψ ξ = group-hom= $ λ= λ _ → H.assoc _ _ _

        inv-l : ∀ φ → comp (inv φ) φ == ident
        inv-l φ = group-hom= $ λ= λ _ → H.inv-l _

        inv-r : ∀ φ → comp φ (inv φ) == ident
        inv-r φ = group-hom= $ λ= λ _ → H.inv-r _

  hom-group : Group (lmax i j)
  hom-group = group (G →ᴳ H.grp) GroupHom-level hom-group-structure

  abstract
    hom-group-is-abelian : is-abelian hom-group
    hom-group-is-abelian φ ψ = group-hom= $ λ= λ g → H.comm _ _

  hom-abgroup : AbGroup (lmax i j)
  hom-abgroup = hom-group , hom-group-is-abelian

pre∘ᴳ-hom : ∀ {i j k} {G : Group i} {H : Group j} (K : AbGroup k)
  → (G →ᴳ H) → (hom-group H K →ᴳ hom-group G K)
pre∘ᴳ-hom K φ = record { f = _∘ᴳ φ ; pres-comp = λ _ _ → group-hom= $ λ= λ _ → idp }
