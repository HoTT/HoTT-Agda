{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation

module lib.groups.Homomorphisms where

idhom : ∀ {i} (G : Group i) → GroupHom G G
idhom G = group-hom (idf _) idp (λ _ _ → idp)

_∘hom_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → GroupHom H K → GroupHom G H → GroupHom G K
(group-hom g g-id g-comp) ∘hom (group-hom f f-id f-comp) =
  record {
    f = g ∘ f;
    pres-ident = ap g f-id ∙ g-id;
    pres-comp = λ x₁ x₂ → ap g (f-comp x₁ x₂) ∙ g-comp (f x₁) (f x₂)}

{- homomorphism preserves inverse -}
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

{- a homomorphism which is an equivalence gives a path between groups -}
module _ {i} {G H : Group i} (φ : GroupHom G H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

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
    group-iso : is-equiv φ.f → G == H
    group-iso e =
      ap3-lemma group
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
            =⟨ ! (to-transp (↓-idf-ua-in _ idp))
               |in-ctx (λ w → H.comp (φ.f a) w) ⟩
          H.comp (φ.f a) (transport (λ C → C) (ua (φ.f , e)) b) ∎

      comp= : G.comp == H.comp [ (λ C → C → C → C) ↓ ua (φ.f , e) ]
      comp= =
        ↓-→-from-transp $ λ= $ λ a →
          transport (λ C → C → C) (ua (φ.f , e)) (G.comp a)
            =⟨ to-transp (comp=' a) ⟩
          H.comp (φ.f a)
            =⟨ ! (to-transp (↓-idf-ua-in _ idp)) |in-ctx (λ w → H.comp w) ⟩
          H.comp (transport (λ C → C) (ua (φ.f , e)) a) ∎

    group-iso-el : (ie : is-equiv φ.f)
      → ap Group.El (group-iso ie) == ua (φ.f , ie)
    group-iso-el e = ap3-lemma-el (ua (φ.f , e)) _ _

{- equality of homomorphisms -}
abstract
  hom= : ∀ {i j} {G : Group i} {H : Group j} (φ ψ : GroupHom G H)
    → GroupHom.f φ == GroupHom.f ψ → φ == ψ
  hom= {H = H} _ _ p =
    ap (λ {(χ , (χ-id , χ-comp)) → group-hom χ χ-id χ-comp})
       (pair= p
         (prop-has-all-paths-↓
           (×-level (Group.El-level H _ _)
                    (Π-level (λ _ → Π-level (λ _ → Group.El-level H _ _))))))

  hom=-↓ : ∀ {i j k} {A : Type i} {G : A → Group j} {H : A → Group k} {x y : A}
    {p : x == y} (φ : GroupHom (G x) (H x)) (ψ : GroupHom (G y) (H y))
    → GroupHom.f φ == GroupHom.f ψ
      [ (λ a → Group.El (G a) → Group.El (H a)) ↓ p ]
    → φ == ψ [ (λ a → GroupHom (G a) (H a)) ↓ p ]
  hom=-↓ {p = idp} = hom=

{- homomorphism with kernel zero is injective -}
module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

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
        =⟨ grouphom-pres-inv φ g₁ |in-ctx (λ w → H.comp w (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₁)) (φ.f g₂)
        =⟨ p |in-ctx (λ w → H.comp (H.inv w) (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₂)) (φ.f g₂)
        =⟨ H.invl (φ.f g₂) ⟩
      H.ident ∎)

{- constant homomorphism -}
module _ where
  cst-hom : ∀ {i j} {G : Group i} {H : Group j} → GroupHom G H
  cst-hom {H = H} = group-hom (cst ident) idp (λ _ _ → ! (unitl _))
    where open Group H

  pre∘-cst-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
    (φ : GroupHom H K)
    → φ ∘hom cst-hom {G = G} {H = H} == cst-hom
  pre∘-cst-hom φ = hom= _ _ (λ= (λ g → GroupHom.pres-ident φ))

{- if an injective homomorphism is merely surjective, then it is
 - fully surjective -}
module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (msurj : (h : H.El) → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h))) where


{- a surjective and injective homomorphism is an isomorphism -}
module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h))) where

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


module _ {i} {G H : Group i} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h))) where

    surj-inj-iso : G == H
    surj-inj-iso = group-iso φ (surj-inj-is-equiv φ inj surj)

{- negation is a homomorphism in an abelian gruop -}
module _ {i} (G : Group i) (G-abelian : is-abelian G) where

  private
    module G = Group G

  inv-hom : GroupHom G G
  inv-hom = record {
    f = G.inv;
    pres-ident = group-inv-ident G;
    pres-comp = λ g₁ g₂ →
      group-inv-comp G g₁ g₂ ∙ G-abelian (G.inv g₂) (G.inv g₁)}

{- two homomorphisms into an abelian group can be composed with
 - the group operation -}
module _ {i} {G H : Group i} (H-abelian : is-abelian H)
  (φ ψ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ
    module ψ = GroupHom ψ

  comp-hom : GroupHom G H
  comp-hom = record {
    f = λ g → H.comp (φ.f g) (ψ.f g);
    pres-ident = ap2 H.comp φ.pres-ident ψ.pres-ident ∙ H.unitl H.ident;
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
       where _□_ = H.comp
