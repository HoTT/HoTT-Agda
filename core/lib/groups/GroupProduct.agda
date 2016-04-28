{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Bool
open import lib.types.Nat
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

infix 80 _×ᴳ_
_×ᴳ_ : ∀ {i j} → Group i → Group j → Group (lmax i j)
_×ᴳ_ (group A A-level A-struct) (group B B-level B-struct) =
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

Πᴳ : ∀ {i j} (I : Type i) (F : I → Group j) → Group (lmax i j)
Πᴳ I F = group (Π I (El ∘ F)) (Π-level (λ i → El-level (F i)))
               (Π-group-struct (group-struct ∘ F))
  where open Group


{- the product of abelian groups is abelian -}
×ᴳ-abelian : ∀ {i j} {G : Group i} {H : Group j}
  → is-abelian G → is-abelian H → is-abelian (G ×ᴳ H)
×ᴳ-abelian aG aH (g₁ , h₁) (g₂ , h₂) = pair×= (aG g₁ g₂) (aH h₁ h₂)

Πᴳ-abelian : ∀ {i j} {I : Type i} {F : I → Group j}
  → (∀ i → is-abelian (F i)) → is-abelian (Πᴳ I F)
Πᴳ-abelian aF f₁ f₂ = λ= (λ i → aF i (f₁ i) (f₂ i))

{- defining a homomorphism into a product -}
×ᴳ-hom-in : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (G →ᴳ H) → (G →ᴳ K) → (G →ᴳ H ×ᴳ K)
×ᴳ-hom-in (group-hom h h-comp) (group-hom k k-comp) = record {
  f = λ x → (h x , k x);
  pres-comp = λ x y → pair×= (h-comp x y) (k-comp x y)}

Πᴳ-hom-in : ∀ {i j k} {I : Type i} {G : Group j} {F : I → Group k}
  → ((i : I) → G →ᴳ F i) → (G →ᴳ Πᴳ I F)
Πᴳ-hom-in h = record {
  f = λ x i → GroupHom.f (h i) x;
  pres-comp = λ x y → λ= (λ i → GroupHom.pres-comp (h i) x y)}

×ᴳ-hom-in-pre∘ : ∀ {i j k l}
  {G : Group i} {H : Group j} {K : Group k} {J : Group l}
  (φ : G →ᴳ H) (ψ : G →ᴳ K) (χ : J →ᴳ G)
  → ×ᴳ-hom-in φ ψ ∘ᴳ χ == ×ᴳ-hom-in (φ ∘ᴳ χ) (ψ ∘ᴳ χ)
×ᴳ-hom-in-pre∘ φ ψ χ = hom= _ _ idp

{- projection homomorphisms -}
×ᴳ-fst : ∀ {i j} {G : Group i} {H : Group j} → (G ×ᴳ H →ᴳ G)
×ᴳ-fst = record {f = fst; pres-comp = λ _ _ → idp}

×ᴳ-snd : ∀ {i j} {G : Group i} {H : Group j} → (G ×ᴳ H →ᴳ H)
×ᴳ-snd = record {f = snd; pres-comp = λ _ _ → idp}

Πᴳ-proj : ∀ {i j} {I : Type i} {F : I → Group j} (i : I)
  → (Πᴳ I F →ᴳ F i)
Πᴳ-proj i = record {
  f = λ f → f i;
  pres-comp = λ _ _ → idp}

{- injection homomorphisms -}
module _ {i j} {G : Group i} {H : Group j} where

  ×ᴳ-inl : G →ᴳ G ×ᴳ H
  ×ᴳ-inl = ×ᴳ-hom-in (idhom G) cst-hom

  ×ᴳ-inr : H →ᴳ G ×ᴳ H
  ×ᴳ-inr = ×ᴳ-hom-in (cst-hom {H = G}) (idhom H)

×ᴳ-diag : ∀ {i} {G : Group i} → (G →ᴳ G ×ᴳ G)
×ᴳ-diag = ×ᴳ-hom-in (idhom _) (idhom _)

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
       where
        infix 80 _□_
        _□_ = G.comp

  ×ᴳ-sum-hom : (H →ᴳ G) → (K →ᴳ G) → (H ×ᴳ K →ᴳ G)
  ×ᴳ-sum-hom φ ψ = record {
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

abstract
  ×ᴳ-sum-hom-η : ∀ {i j} (G : Group i) (H : Group j)
    (aGH : is-abelian (G ×ᴳ H))
    → idhom (G ×ᴳ H) == ×ᴳ-sum-hom aGH (×ᴳ-inl {G = G}) (×ᴳ-inr {G = G})
  ×ᴳ-sum-hom-η G H aGH = hom= _ _ $ λ= $ λ {(g , h) →
    ! (pair×= (Group.unitr G g) (Group.unitl H h))}

  ∘-×ᴳ-sum-hom : ∀ {i j k l}
    {G : Group i} {H : Group j} {K : Group k} {L : Group l}
    (aK : is-abelian K) (aL : is-abelian L)
    (φ : K →ᴳ L) (ψ : G →ᴳ K) (χ : H →ᴳ K)
    → ×ᴳ-sum-hom aL (φ ∘ᴳ ψ) (φ ∘ᴳ χ) == φ ∘ᴳ (×ᴳ-sum-hom aK ψ χ)
  ∘-×ᴳ-sum-hom aK aL φ ψ χ = hom= _ _ $ λ= $ λ {(g , h) →
    ! (GroupHom.pres-comp φ (GroupHom.f ψ g) (GroupHom.f χ h))}

{- define a homomorphism G₁ × G₂ → H₁ × H₂ from homomorphisms
 - G₁ → H₁ and G₂ → H₂ -}
×ᴳ-parallel-hom : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → (G₁ →ᴳ H₁) → (G₂ →ᴳ H₂) → (G₁ ×ᴳ G₂ →ᴳ H₁ ×ᴳ H₂)
×ᴳ-parallel-hom φ ψ = record {
  f = λ {(h₁ , h₂) → (φ.f h₁ , ψ.f h₂)};
  pres-comp = λ {(h₁ , h₂) (h₁' , h₂') →
    pair×= (φ.pres-comp h₁ h₁') (ψ.pres-comp h₂ h₂')}}
  where
  module φ = GroupHom φ
  module ψ = GroupHom ψ

{- 0ᴳ is a unit for product -}
×ᴳ-unit-l : ∀ {i} {G : Group i} → 0ᴳ {i} ×ᴳ G == G
×ᴳ-unit-l = group-ua
  (×ᴳ-snd {G = 0ᴳ} ,
   is-eq snd (λ g → (lift unit , g)) (λ _ → idp) (λ _ → idp))

×ᴳ-unit-r : ∀ {i} {G : Group i} → G ×ᴳ 0ᴳ {i} == G
×ᴳ-unit-r = group-ua
  (×ᴳ-fst , (is-eq fst (λ g → (g , lift unit)) (λ _ → idp) (λ _ → idp)))

{- A product Πᴳ indexed by Bool is the same as a binary product -}
module _ {i} (Pick : Lift {j = i} Bool → Group i) where

  Πᴳ-Bool-is-×ᴳ :
    Πᴳ (Lift Bool) Pick == (Pick (lift true)) ×ᴳ (Pick (lift false))
  Πᴳ-Bool-is-×ᴳ = group-ua (φ , e)
    where
    φ = ×ᴳ-hom-in (Πᴳ-proj {F = Pick} (lift true))
                  (Πᴳ-proj {F = Pick} (lift false))

    e : is-equiv (GroupHom.f φ)
    e = is-eq _ (λ {(g , h) → λ {(lift true) → g; (lift false) → h}})
          (λ _ → idp)
          (λ _ → λ= (λ {(lift true) → idp; (lift false) → idp}))

{- Commutativity of ×ᴳ -}
×ᴳ-comm : ∀ {i j} (H : Group i) (K : Group j) → H ×ᴳ K ≃ᴳ K ×ᴳ H
×ᴳ-comm H K =
  (record {
     f = λ {(h , k) → (k , h)};
     pres-comp = λ _ _ → idp} ,
   snd (equiv _ (λ {(k , h) → (h , k)}) (λ _ → idp) (λ _ → idp)))

{- Associativity of ×ᴳ -}
×ᴳ-assoc : ∀ {i j k} (G : Group i) (H : Group j) (K : Group k)
  → ((G ×ᴳ H) ×ᴳ K) == (G ×ᴳ (H ×ᴳ K))
×ᴳ-assoc G H K = group-ua
  (record {
     f = λ {((g , h) , k) → (g , (h , k))};
     pres-comp = λ _ _ → idp} ,
   snd (equiv _ (λ {(g , (h , k)) → ((g , h) , k)}) (λ _ → idp) (λ _ → idp)))

module _ {i} where

  infixl 80 _^ᴳ_
  _^ᴳ_ : Group i → ℕ → Group i
  H ^ᴳ O = 0ᴳ
  H ^ᴳ (S n) = H ×ᴳ (H ^ᴳ n)

  ^ᴳ-sum : (H : Group i) (m n : ℕ) → (H ^ᴳ m) ×ᴳ (H ^ᴳ n) == H ^ᴳ (m + n)
  ^ᴳ-sum H O n = ×ᴳ-unit-l {G = H ^ᴳ n}
  ^ᴳ-sum H (S m) n =
    ×ᴳ-assoc H (H ^ᴳ m) (H ^ᴳ n) ∙ ap (λ K → H ×ᴳ K) (^ᴳ-sum H m n)
