{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation

module lib.groups.Homomorphisms where

record GroupHom {i j} (G : Group i) (H : Group j)
  : Type (lsucc (lmax i j)) where
  constructor group-hom

  field
    f : Group.El G → Group.El H
    pres-comp  : ∀ g1 g2 → f (Group.comp G g1 g2) == Group.comp H (f g1) (f g2)

  abstract
    pres-ident : f (Group.ident G) == Group.ident H
    pres-ident = group-cancel-l H (f (Group.ident G)) $
      Group.comp H (f (Group.ident G)) (f (Group.ident G))
        =⟨ ! (pres-comp (Group.ident G) (Group.ident G)) ⟩
      f (Group.comp G (Group.ident G) (Group.ident G))
        =⟨ ap f (Group.unitl G (Group.ident G)) ⟩
      f (Group.ident G)
        =⟨ ! (Group.unitr H (f (Group.ident G))) ⟩
      Group.comp H (f (Group.ident G)) (Group.ident H) ∎

    pres-inv : (g : Group.El G) → f (Group.inv G g) == Group.inv H (f g)
    pres-inv g =
      f (Group.inv G g)
        =⟨ ! (Group.unitr H (f (Group.inv G g))) ⟩
      Group.comp H (f (Group.inv G g)) (Group.ident H)
        =⟨ ! (Group.invr H (f g))
           |in-ctx (λ w → Group.comp H (f (Group.inv G g)) w) ⟩
      Group.comp H (f (Group.inv G g)) (Group.comp H (f g) (Group.inv H (f g)))
        =⟨ ! (Group.assoc H (f (Group.inv G g)) (f g) (Group.inv H (f g))) ⟩
      Group.comp H (Group.comp H (f (Group.inv G g)) (f g)) (Group.inv H (f g))
        =⟨ ! (pres-comp (Group.inv G g) g) ∙ ap f (Group.invl G g) ∙ pres-ident
           |in-ctx (λ w → Group.comp H w (Group.inv H (f g))) ⟩
      Group.comp H (Group.ident H) (Group.inv H (f g))
        =⟨ Group.unitl H (Group.inv H (f g)) ⟩
      Group.inv H (f g) ∎

  ⊙f : Σ (Group.El G → Group.El H)
            (λ f → f (Group.ident G) == Group.ident H)
  ⊙f = (f , pres-ident)

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

GroupIso : ∀ {i j} (G : Group i) (H : Group j) → Type (lsucc (lmax i j))
GroupIso G H = Σ (G →ᴳ H) (λ φ → is-equiv (GroupHom.f φ))

infix 30 _≃ᴳ_
_≃ᴳ_ = GroupIso

idhom : ∀ {i} (G : Group i) → (G →ᴳ G)
idhom G = group-hom (idf _) (λ _ _ → idp)

idiso : ∀ {i} (G : Group i) → (G ≃ᴳ G)
idiso G = (idhom G , idf-is-equiv _)

infixr 80 _∘ᴳ_

_∘ᴳ_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (H →ᴳ K) → (G →ᴳ H) → (G →ᴳ K)
(group-hom g g-comp) ∘ᴳ (group-hom f f-comp) =
  record {
    f = g ∘ f;
    pres-comp = λ x₁ x₂ → ap g (f-comp x₁ x₂) ∙ g-comp (f x₁) (f x₂)}

infixr 80 _∘eᴳ_

_∘eᴳ_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → H ≃ᴳ K → G ≃ᴳ H → G ≃ᴳ K
(φ₂ , ie₂) ∘eᴳ (φ₁ , ie₁) = (φ₂ ∘ᴳ φ₁ , ie₂ ∘ise ie₁)

infixl 120 _⁻¹ᴳ

_⁻¹ᴳ : ∀ {i j} {G : Group i} {H : Group j} → G ≃ᴳ H → H ≃ᴳ G
_⁻¹ᴳ {G = G} {H = H} (φ , ie) =
  (record {
     f = is-equiv.g ie;
     pres-comp = λ h₁ h₂ →
       ap2 (λ w₁ w₂ → is-equiv.g ie (Group.comp H w₁ w₂))
         (! (is-equiv.f-g ie h₁)) (! (is-equiv.f-g ie h₂))
       ∙ ! (ap (is-equiv.g ie)
               (GroupHom.pres-comp φ (is-equiv.g ie h₁) (is-equiv.g ie h₂)))
       ∙ is-equiv.g-f ie (Group.comp G (is-equiv.g ie h₁) (is-equiv.g ie h₂))} ,
   snd ((_ , ie) ⁻¹))

{- a homomorphism which is an equivalence gives a path between groups -}
module _ {i} {G H : Group i} (iso : G ≃ᴳ H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom (fst iso)
    ie = snd iso

  private
    ap3-lemma : ∀ {i j k l} {C : Type i} {D : C → Type j} {E : C → Type k}
      {F : Type l} {c₁ c₂ : C} {d₁ : D c₁} {d₂ : D c₂} {e₁ : E c₁} {e₂ : E c₂}
      (f : (c : C) → D c → E c → F) (p : c₁ == c₂)
      → (d₁ == d₂ [ D ↓ p ]) → (e₁ == e₂ [ E ↓ p ])
      → (f c₁ d₁ e₁ == f c₂ d₂ e₂)
    ap3-lemma f idp idp idp = idp

    ap3-lemma-el : ∀ {i} {G H : Group i}
      (p : Group.El G == Group.El H)
      (q : Group.El-level G == Group.El-level H [ _ ↓ p ])
      (r : Group.group-struct G == Group.group-struct H [ _ ↓ p ])
      → ap Group.El (ap3-lemma group p q r) == p
    ap3-lemma-el idp idp idp = idp

  abstract
    group-ua : G == H
    group-ua =
      ap3-lemma group
        (ua (φ.f , ie))
        (prop-has-all-paths-↓ has-level-is-prop)
        (↓-group-structure= (G.El-level) (ua (φ.f , ie)) ident= inv= comp=)
      where
      ident= : G.ident == H.ident [ (λ C → C) ↓ ua (φ.f , ie) ]
      ident= = ↓-idf-ua-in _ φ.pres-ident

      inv= : G.inv == H.inv [ (λ C → C → C) ↓ ua (φ.f , ie) ]
      inv= =
        ↓-→-from-transp $ λ= $ λ a →
          transport (λ C → C) (ua (φ.f , ie)) (G.inv a)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          φ.f (G.inv a)
            =⟨ φ.pres-inv a ⟩
          H.inv (φ.f a)
            =⟨ ap H.inv (! (to-transp (↓-idf-ua-in _ idp))) ⟩
          H.inv (transport (λ C → C) (ua (φ.f , ie)) a) ∎

      comp=' : (a : G.El)
        → G.comp a == H.comp (φ.f a) [ (λ C → C → C) ↓ ua (φ.f , ie) ]
      comp=' a =
        ↓-→-from-transp $ λ= $ λ b →
          transport (λ C → C) (ua (φ.f , ie)) (G.comp a b)
            =⟨ to-transp (↓-idf-ua-in _ idp) ⟩
          φ.f (G.comp a b)
            =⟨ φ.pres-comp a b ⟩
          H.comp (φ.f a) (φ.f b)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp))
               |in-ctx (λ w → H.comp (φ.f a) w) ⟩
          H.comp (φ.f a) (transport (λ C → C) (ua (φ.f , ie)) b) ∎

      comp= : G.comp == H.comp [ (λ C → C → C → C) ↓ ua (φ.f , ie) ]
      comp= =
        ↓-→-from-transp $ λ= $ λ a →
          transport (λ C → C → C) (ua (φ.f , ie)) (G.comp a)
            =⟨ to-transp (comp=' a) ⟩
          H.comp (φ.f a)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → H.comp w) ⟩
          H.comp (transport (λ C → C) (ua (φ.f , ie)) a) ∎

    group-ua-el : ap Group.El group-ua == ua (φ.f , ie)
    group-ua-el = ap3-lemma-el (ua (φ.f , ie)) _ _

-- XXX TODO rename [hom=] to [hom=-in]
{- equality of homomorphisms -}
abstract
  hom= : ∀ {i j} {G : Group i} {H : Group j} (φ ψ : (G →ᴳ H))
    → GroupHom.f φ == GroupHom.f ψ → φ == ψ
  hom= {H = H} _ _ p =
   ap (uncurry group-hom)
      (pair= p (prop-has-all-paths-↓
                 (Π-level (λ _ → Π-level (λ _ → Group.El-level H _ _)))))

  hom=-↓ : ∀ {i j k} {A : Type i} {G : A → Group j} {H : A → Group k} {x y : A}
    {p : x == y} (φ : G x →ᴳ H x) (ψ : G y →ᴳ H y)
    → GroupHom.f φ == GroupHom.f ψ
      [ (λ a → Group.El (G a) → Group.El (H a)) ↓ p ]
    → φ == ψ [ (λ a → G a →ᴳ H a) ↓ p ]
  hom=-↓ {p = idp} = hom=

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
  → coeᴳ (group-ua iso) == fst iso
coeᴳ-β (φ , ie) = hom= _ _ $
  coeᴳ-fun (group-ua (φ , ie))
  ∙ ap coe (group-ua-el (φ , ie))
  ∙ λ= (coe-β (GroupHom.f φ , ie))

{- algebraic properties -}

∘ᴳ-unit-r : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → φ ∘ᴳ idhom G == φ
∘ᴳ-unit-r φ = idp

∘ᴳ-unit-l : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → idhom H ∘ᴳ φ == φ
∘ᴳ-unit-l φ = hom= _ _ $ idp

∘ᴳ-assoc : ∀ {i j k l} {G : Group i} {H : Group j} {K : Group k} {L : Group l}
  (χ : K →ᴳ L) (ψ : H →ᴳ K) (φ : G →ᴳ H)
  → (χ ∘ᴳ ψ) ∘ᴳ φ == χ ∘ᴳ ψ ∘ᴳ φ
∘ᴳ-assoc χ ψ φ = hom= _ _ $ idp

{- homomorphism with kernel zero is injective -}
module _ {i j} {G : Group i} {H : Group j} (φ : (G →ᴳ H)) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  zero-kernel-injective : ((g : G.El) → φ.f g == H.ident → g == G.ident)
    → ((g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
  zero-kernel-injective f g₁ g₂ p =
    ! (group-inv-inv G g₁) ∙ group-inv-unique-r G (G.inv g₁) g₂ (f _ $
      φ.f (G.comp (G.inv g₁) g₂)
        =⟨ φ.pres-comp (G.inv g₁) g₂ ⟩
      H.comp (φ.f (G.inv g₁)) (φ.f g₂)
        =⟨ φ.pres-inv g₁ |in-ctx (λ w → H.comp w (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₁)) (φ.f g₂)
        =⟨ p |in-ctx (λ w → H.comp (H.inv w) (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₂)) (φ.f g₂)
        =⟨ H.invl (φ.f g₂) ⟩
      H.ident ∎)

{- constant homomorphism -}
module _ where
  cst-hom : ∀ {i j} {G : Group i} {H : Group j} → (G →ᴳ H)
  cst-hom {H = H} = group-hom (cst ident) (λ _ _ → ! (unitl _))
    where open Group H

  pre∘-cst-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
    (φ : H →ᴳ K)
    → φ ∘ᴳ cst-hom {G = G} {H = H} == cst-hom
  pre∘-cst-hom φ = hom= _ _ (λ= (λ g → GroupHom.pres-ident φ))

{- if an injective homomorphism is merely surjective, then it is
 - fully surjective -}
module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (msurj : (h : H.El) → Trunc -1 (Σ G.El (λ g → φ.f g == h))) where


{- a surjective and injective homomorphism is an isomorphism -}
module _ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

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


module _ {i} {G H : Group i} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Trunc -1 (Σ G.El (λ g → φ.f g == h))) where

    surj-inj-iso : G ≃ᴳ H
    surj-inj-iso = (φ , surj-inj-is-equiv φ inj surj)

    surj-inj-path : G == H
    surj-inj-path = group-ua surj-inj-iso

{- negation is a homomorphism in an abelian gruop -}
inv-hom : ∀ {i} (G : Group i) (G-abelian : is-abelian G) → GroupHom G G
inv-hom G G-abelian = record {
  f = Group.inv G;
  pres-comp = λ g₁ g₂ →
    group-inv-comp G g₁ g₂ ∙ G-abelian (Group.inv G g₂) (Group.inv G g₁)}

inv-hom-natural : ∀ {i j} {G : Group i} {H : Group j}
  (G-abelian : is-abelian G) (H-abelian : is-abelian H) (φ : G →ᴳ H)
  → φ ∘ᴳ inv-hom G G-abelian == inv-hom H H-abelian ∘ᴳ φ
inv-hom-natural _ _ φ = hom= _ _ $ λ= $ GroupHom.pres-inv φ

{- two homomorphisms into an abelian group can be composed with
 - the group operation -}
module _ {i} {G H : Group i} (H-abelian : is-abelian H)
  (φ ψ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ
    module ψ = GroupHom ψ

  comp-hom : G →ᴳ H
  comp-hom = record {
    f = λ g → H.comp (φ.f g) (ψ.f g);
    pres-comp = λ g₁ g₂ →
      H.comp (φ.f (G.comp g₁ g₂)) (ψ.f (G.comp g₁ g₂))
        =⟨ ap2 H.comp (φ.pres-comp g₁ g₂) (ψ.pres-comp g₁ g₂) ⟩
      H.comp (H.comp (φ.f g₁) (φ.f g₂)) (H.comp (ψ.f g₁) (ψ.f g₂))
        =⟨ lemma (φ.f g₁) (φ.f g₂) (ψ.f g₁) (ψ.f g₂) ⟩
      H.comp (H.comp (φ.f g₁) (ψ.f g₁)) (H.comp (φ.f g₂) (ψ.f g₂)) ∎}

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
       (h₁ □ h₃) □ (h₂ □ h₄) ∎
       where
        infix 80 _□_
        _□_ = H.comp
