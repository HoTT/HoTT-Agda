{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Bool
open import lib.types.Pi
open import lib.types.Sigma
open import lib.groups.Homomorphisms
open import lib.groups.Lift
open import lib.groups.Unit

module lib.groups.GroupProduct where

{- binary product -}
×-group-struct : ∀ {i j} {A : Type i} {B : Type j}
  (GS : GroupStructure A) (HS : GroupStructure B)
  → GroupStructure (A × B)
×-group-struct GS HS = record {
  ident = (ident GS , ident HS);
  inv = λ {(g , h) → (inv GS g , inv HS h)};
  comp = λ {(g₁ , h₁) (g₂ , h₂) → (comp GS g₁ g₂ , comp HS h₁ h₂)};
  unitl = λ {(g , h) → pair×= (unitl GS g) (unitl HS h)};
  unitr = λ {(g , h) → pair×= (unitr GS g) (unitr HS h)};
  assoc = λ {(g₁ , h₁) (g₂ , h₂) (g₃ , h₃) →
    pair×= (assoc GS g₁ g₂ g₃) (assoc HS h₁ h₂ h₃)};
  invl = λ {(g , h) → pair×= (invl GS g) (invl HS h)};
  invr = λ {(g , h) → pair×= (invr GS g) (invr HS h)}}
  where open GroupStructure

_×G_ : ∀ {i j} → Group i → Group j → Group (lmax i j)
_×G_ (group A A-level A-struct) (group B B-level B-struct) =
  group (A × B) (×-level A-level B-level) (×-group-struct A-struct B-struct)


{- general product -}
Π-group-struct : ∀ {i j} {I : Type i} {A : I → Type j}
  (FS : (i : I) → GroupStructure (A i))
  → GroupStructure (Π I A)
Π-group-struct FS = record {
  ident = ident ∘ FS;
  inv = λ f i → inv (FS i) (f i);
  comp = λ f g i → comp (FS i) (f i) (g i);
  unitl = λ f → (λ= (λ i → unitl (FS i) (f i)));
  unitr = λ f → (λ= (λ i → unitr (FS i) (f i)));
  assoc = λ f g h → (λ= (λ i → assoc (FS i) (f i) (g i) (h i)));
  invl = λ f → (λ= (λ i → invl (FS i) (f i)));
  invr = λ f → (λ= (λ i → invr (FS i) (f i)))}
  where open GroupStructure

ΠG : ∀ {i j} (I : Type i) (F : I → Group j) → Group (lmax i j)
ΠG I F = group (Π I (El ∘ F)) (Π-level (λ i → El-level (F i)))
               (Π-group-struct (group-struct ∘ F))
  where open Group


{- the product of abelian groups is abelian -}
×G-abelian : ∀ {i j} {G : Group i} {H : Group j}
  → is-abelian G → is-abelian H → is-abelian (G ×G H)
×G-abelian aG aH (g₁ , h₁) (g₂ , h₂) = pair×= (aG g₁ g₂) (aH h₁ h₂)

ΠG-abelian : ∀ {i j} {I : Type i} {F : I → Group j}
  → (∀ i → is-abelian (F i)) → is-abelian (ΠG I F)
ΠG-abelian aF f₁ f₂ = λ= (λ i → aF i (f₁ i) (f₂ i))

{- defining a homomorphism into a binary product -}
×-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → GroupHom G H → GroupHom G K → GroupHom G (H ×G K)
×-hom (group-hom h h-comp) (group-hom k k-comp) = record {
  f = λ x → (h x , k x);
  pres-comp = λ x y → pair×= (h-comp x y) (k-comp x y)}

{- projection homomorphisms -}
×G-fst : ∀ {i j} {G : Group i} {H : Group j} → GroupHom (G ×G H) G
×G-fst = record {f = fst; pres-comp = λ _ _ → idp}

×G-snd : ∀ {i j} {G : Group i} {H : Group j} → GroupHom (G ×G H) H
×G-snd = record {f = snd; pres-comp = λ _ _ → idp}

ΠG-proj : ∀ {i j} {I : Type i} {F : I → Group j} (i : I)
  → GroupHom (ΠG I F) (F i)
ΠG-proj i = record {
  f = λ f → f i;
  pres-comp = λ _ _ → idp}

{- injection homomorphisms -}
module _ {i j} {G : Group i} {H : Group j} where

  ×G-inl : GroupHom G (G ×G H)
  ×G-inl = ×-hom (idhom G) cst-hom

  ×G-inr : GroupHom H (G ×G H)
  ×G-inr = ×-hom (cst-hom {H = G}) (idhom H)

{- when G is abelian, we can define a map H×K → G as a sum of maps
 - H → G and K → G (that is, the product behaves as a sum)         -}
module _ {i j k} {G : Group i} {H : Group j} {K : Group k}
  (G-abelian : is-abelian G) where

  private
    module G = Group G
    module H = Group H
    module K = Group K

    lemma : (g₁ g₂ g₃ g₄ : G.El) →
      G.comp (G.comp g₁ g₂) (G.comp g₃ g₄)
      == G.comp (G.comp g₁ g₃) (G.comp g₂ g₄)
    lemma g₁ g₂ g₃ g₄ =
      (g₁ □ g₂) □ (g₃ □ g₄)
         =⟨ G.assoc g₁ g₂ (g₃ □ g₄) ⟩
       g₁ □ (g₂ □ (g₃ □ g₄))
         =⟨ G-abelian g₃ g₄ |in-ctx (λ w → g₁ □ (g₂ □ w)) ⟩
       g₁ □ (g₂ □ (g₄ □ g₃))
         =⟨ ! (G.assoc g₂ g₄ g₃) |in-ctx (λ w → g₁ □ w) ⟩
       g₁ □ ((g₂ □ g₄) □ g₃)
         =⟨ G-abelian (g₂ □ g₄) g₃ |in-ctx (λ w → g₁ □ w) ⟩
       g₁ □ (g₃ □ (g₂ □ g₄))
         =⟨ ! (G.assoc g₁ g₃ (g₂ □ g₄)) ⟩
       (g₁ □ g₃) □ (g₂ □ g₄) ∎
       where _□_ = G.comp

  ×-sum-hom : GroupHom H G → GroupHom K G → GroupHom (H ×G K) G
  ×-sum-hom φ ψ = record {
    f = λ {(h , k) → G.comp (φ.f h) (ψ.f k)};

    pres-comp = λ {(h₁ , k₁) (h₂ , k₂) →
      G.comp (φ.f (H.comp h₁ h₂)) (ψ.f (K.comp k₁ k₂))
        =⟨ φ.pres-comp h₁ h₂ |in-ctx (λ w → G.comp w (ψ.f (K.comp k₁ k₂))) ⟩
      G.comp (G.comp (φ.f h₁) (φ.f h₂)) (ψ.f (K.comp k₁ k₂))
        =⟨ ψ.pres-comp k₁ k₂
           |in-ctx (λ w → G.comp (G.comp (φ.f h₁) (φ.f h₂)) w)  ⟩
      G.comp (G.comp (φ.f h₁) (φ.f h₂)) (G.comp (ψ.f k₁) (ψ.f k₂))
        =⟨ lemma (φ.f h₁) (φ.f h₂) (ψ.f k₁) (ψ.f k₂) ⟩
      G.comp (G.comp (φ.f h₁) (ψ.f k₁)) (G.comp (φ.f h₂) (ψ.f k₂)) ∎}}
      where
      module φ = GroupHom φ
      module ψ = GroupHom ψ

{- define a homomorphism G₁ × G₂ → H₁ × H₂ from homomorphisms
 - G₁ → H₁ and G₂ → H₂ -}
×-parallel-hom : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → GroupHom G₁ H₁ → GroupHom G₂ H₂ → GroupHom (G₁ ×G G₂) (H₁ ×G H₂)
×-parallel-hom φ ψ = record {
  f = λ {(h₁ , h₂) → (φ.f h₁ , ψ.f h₂)};
  pres-comp = λ {(h₁ , h₂) (h₁' , h₂') →
    pair×= (φ.pres-comp h₁ h₁') (ψ.pres-comp h₂ h₂')}}
  where
  module φ = GroupHom φ
  module ψ = GroupHom ψ

{- 0G is a unit for product -}
×G-unit-l : ∀ {i} {G : Group i} → 0G {i} ×G G == G
×G-unit-l = group-iso
  (×G-snd {G = 0G})
  (is-eq snd (λ g → (lift unit , g)) (λ _ → idp) (λ _ → idp))

×G-unit-r : ∀ {i} {G : Group i} → G ×G 0G {i} == G
×G-unit-r = group-iso
  ×G-fst (is-eq fst (λ g → (g , lift unit)) (λ _ → idp) (λ _ → idp))

{- A product ΠG indexed by Bool is the same as a binary product -}
module _ {i} (Pick : Lift {j = i} Bool → Group i) where

  ΠG-Bool-is-×G : ΠG (Lift Bool) Pick
               == (Pick (lift true)) ×G (Pick (lift false))
  ΠG-Bool-is-×G = group-iso φ e
    where
    φ = ×-hom (ΠG-proj {F = Pick} (lift true))
              (ΠG-proj {F = Pick} (lift false))

    e : is-equiv (GroupHom.f φ)
    e = is-eq _ (λ {(g , h) → λ {(lift true) → g; (lift false) → h}})
          (λ _ → idp)
          (λ _ → λ= (λ {(lift true) → idp; (lift false) → idp}))
