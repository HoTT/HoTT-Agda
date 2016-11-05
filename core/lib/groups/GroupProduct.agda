{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Group
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism
open import lib.groups.SubgroupProp
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
  unit-l = λ {(g , h) → pair×= (unit-l GS g) (unit-l HS h)};
  unit-r = λ {(g , h) → pair×= (unit-r GS g) (unit-r HS h)};
  assoc = λ {(g₁ , h₁) (g₂ , h₂) (g₃ , h₃) →
    pair×= (assoc GS g₁ g₂ g₃) (assoc HS h₁ h₂ h₃)};
  inv-l = λ {(g , h) → pair×= (inv-l GS g) (inv-l HS h)};
  inv-r = λ {(g , h) → pair×= (inv-r GS g) (inv-r HS h)}}
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
  unit-l = λ f → (λ= (λ i → unit-l (FS i) (f i)));
  unit-r = λ f → (λ= (λ i → unit-r (FS i) (f i)));
  assoc = λ f g h → (λ= (λ i → assoc (FS i) (f i) (g i) (h i)));
  inv-l = λ f → (λ= (λ i → inv-l (FS i) (f i)));
  inv-r = λ f → (λ= (λ i → inv-r (FS i) (f i)))}
  where open GroupStructure

Πᴳ : ∀ {i j} (I : Type i) (F : I → Group j) → Group (lmax i j)
Πᴳ I F = group (Π I (El ∘ F)) (Π-level (λ i → El-level (F i)))
               (Π-group-struct (group-struct ∘ F))
  where open Group

{- functorial behavior of [Πᴳ] -}
Πᴳ-emap-r : ∀ {i j k} (I : Type i) {F : I → Group j} {G : I → Group k}
  → (∀ i → F i ≃ᴳ G i) → Πᴳ I F ≃ᴳ Πᴳ I G
Πᴳ-emap-r I {F} {G} iso = ≃-to-≃ᴳ (Π-emap-r (GroupIso.f-equiv ∘ iso))
  (λ f g → λ= λ i → GroupIso.pres-comp (iso i) (f i) (g i))

{- the product of abelian groups is abelian -}
×ᴳ-abelian : ∀ {i j} {G : Group i} {H : Group j}
  → is-abelian G → is-abelian H → is-abelian (G ×ᴳ H)
×ᴳ-abelian aG aH (g₁ , h₁) (g₂ , h₂) = pair×= (aG g₁ g₂) (aH h₁ h₂)

Πᴳ-abelian : ∀ {i j} {I : Type i} {F : I → Group j}
  → (∀ i → is-abelian (F i)) → is-abelian (Πᴳ I F)
Πᴳ-abelian aF f₁ f₂ = λ= (λ i → aF i (f₁ i) (f₂ i))

{- defining a homomorphism into a product -}
×ᴳ-fanout : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (G →ᴳ H) → (G →ᴳ K) → (G →ᴳ H ×ᴳ K)
×ᴳ-fanout (group-hom h h-comp) (group-hom k k-comp) =
  group-hom
    (λ x → (h x , k x))
    (λ x y → pair×= (h-comp x y) (k-comp x y))

Πᴳ-fanout : ∀ {i j k} {I : Type i} {G : Group j} {F : I → Group k}
  → ((i : I) → G →ᴳ F i) → (G →ᴳ Πᴳ I F)
Πᴳ-fanout h = group-hom
  (λ x i → GroupHom.f (h i) x)
  (λ x y → λ= (λ i → GroupHom.pres-comp (h i) x y))

×ᴳ-fanout-pre∘ : ∀ {i j k l}
  {G : Group i} {H : Group j} {K : Group k} {J : Group l}
  (φ : G →ᴳ H) (ψ : G →ᴳ K) (χ : J →ᴳ G)
  → ×ᴳ-fanout φ ψ ∘ᴳ χ == ×ᴳ-fanout (φ ∘ᴳ χ) (ψ ∘ᴳ χ)
×ᴳ-fanout-pre∘ φ ψ χ = group-hom= idp

{- projection homomorphisms -}
×ᴳ-fst : ∀ {i j} {G : Group i} {H : Group j} → (G ×ᴳ H →ᴳ G)
×ᴳ-fst = group-hom fst (λ _ _ → idp)

×ᴳ-snd : ∀ {i j} {G : Group i} {H : Group j} → (G ×ᴳ H →ᴳ H)
×ᴳ-snd = group-hom snd (λ _ _ → idp)

×ᴳ-snd-is-surj : ∀ {i j} {G : Group i} {H : Group j}
  → is-surjᴳ (×ᴳ-snd {G = G} {H = H})
×ᴳ-snd-is-surj {G = G} h = [ (Group.ident G , h) , idp ]

Πᴳ-proj : ∀ {i j} {I : Type i} {F : I → Group j} (i : I)
  → (Πᴳ I F →ᴳ F i)
Πᴳ-proj i = group-hom (λ f → f i) (λ _ _ → idp)

{- injection homomorphisms -}
module _ {i j} {G : Group i} {H : Group j} where

  ×ᴳ-inl : G →ᴳ G ×ᴳ H
  ×ᴳ-inl = ×ᴳ-fanout (idhom G) cst-hom

  ×ᴳ-inr : H →ᴳ G ×ᴳ H
  ×ᴳ-inr = ×ᴳ-fanout (cst-hom {H = G}) (idhom H)

×ᴳ-diag : ∀ {i} {G : Group i} → (G →ᴳ G ×ᴳ G)
×ᴳ-diag = ×ᴳ-fanout (idhom _) (idhom _)

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
       (g₁ □ g₃) □ (g₂ □ g₄) =∎
       where
        infix 80 _□_
        _□_ = G.comp

  ×ᴳ-fanin : (H →ᴳ G) → (K →ᴳ G) → (H ×ᴳ K →ᴳ G)
  ×ᴳ-fanin φ ψ = group-hom
    (λ {(h , k) → G.comp (φ.f h) (ψ.f k)})
    (λ {(h₁ , k₁) (h₂ , k₂) →
      G.comp (φ.f (H.comp h₁ h₂)) (ψ.f (K.comp k₁ k₂))
        =⟨ φ.pres-comp h₁ h₂ |in-ctx (λ w → G.comp w (ψ.f (K.comp k₁ k₂))) ⟩
      G.comp (G.comp (φ.f h₁) (φ.f h₂)) (ψ.f (K.comp k₁ k₂))
        =⟨ ψ.pres-comp k₁ k₂
           |in-ctx (λ w → G.comp (G.comp (φ.f h₁) (φ.f h₂)) w)  ⟩
      G.comp (G.comp (φ.f h₁) (φ.f h₂)) (G.comp (ψ.f k₁) (ψ.f k₂))
        =⟨ lemma (φ.f h₁) (φ.f h₂) (ψ.f k₁) (ψ.f k₂) ⟩
      G.comp (G.comp (φ.f h₁) (ψ.f k₁)) (G.comp (φ.f h₂) (ψ.f k₂)) =∎})
    where
      module φ = GroupHom φ
      module ψ = GroupHom ψ

abstract
  ×ᴳ-fanin-η : ∀ {i j} (G : Group i) (H : Group j)
    (aGH : is-abelian (G ×ᴳ H))
    → idhom (G ×ᴳ H) == ×ᴳ-fanin aGH (×ᴳ-inl {G = G}) (×ᴳ-inr {G = G})
  ×ᴳ-fanin-η G H aGH = group-hom= $ λ= λ {(g , h) →
    ! (pair×= (Group.unit-r G g) (Group.unit-l H h))}

  ×ᴳ-fanin-pre∘ : ∀ {i j k l}
    {G : Group i} {H : Group j} {K : Group k} {L : Group l}
    (aK : is-abelian K) (aL : is-abelian L)
    (φ : K →ᴳ L) (ψ : G →ᴳ K) (χ : H →ᴳ K)
    → ×ᴳ-fanin aL (φ ∘ᴳ ψ) (φ ∘ᴳ χ) == φ ∘ᴳ (×ᴳ-fanin aK ψ χ)
  ×ᴳ-fanin-pre∘ aK aL φ ψ χ = group-hom= $ λ= λ {(g , h) →
    ! (GroupHom.pres-comp φ (GroupHom.f ψ g) (GroupHom.f χ h))}

{- define a homomorphism [G₁ × G₂ → H₁ × H₂] from homomorphisms
 - [G₁ → H₁] and [G₂ → H₂] -}
×ᴳ-fmap : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → (G₁ →ᴳ H₁) → (G₂ →ᴳ H₂) → (G₁ ×ᴳ G₂ →ᴳ H₁ ×ᴳ H₂)
×ᴳ-fmap φ ψ = group-hom
  (λ {(h₁ , h₂) → (φ.f h₁ , ψ.f h₂)})
  (λ {(h₁ , h₂) (h₁' , h₂') →
    pair×= (φ.pres-comp h₁ h₁') (ψ.pres-comp h₂ h₂')})
  where
    module φ = GroupHom φ
    module ψ = GroupHom ψ

×ᴳ-emap : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → (G₁ ≃ᴳ H₁) → (G₂ ≃ᴳ H₂) → (G₁ ×ᴳ G₂ ≃ᴳ H₁ ×ᴳ H₂)
×ᴳ-emap (φ , φ-is-equiv) (ψ , ψ-is-equiv) =
  ×ᴳ-fmap φ ψ , ×-isemap φ-is-equiv ψ-is-equiv

{- 0ᴳ is a unit for product -}
×ᴳ-unit-l : ∀ {i} (G : Group i) → 0ᴳ ×ᴳ G ≃ᴳ G
×ᴳ-unit-l _ = ×ᴳ-snd {G = 0ᴳ} , is-eq snd (λ g → (unit , g)) (λ _ → idp) (λ _ → idp)

×ᴳ-unit-r : ∀ {i} (G : Group i) → G ×ᴳ 0ᴳ ≃ᴳ G
×ᴳ-unit-r _ = ×ᴳ-fst , is-eq fst (λ g → (g , unit)) (λ _ → idp) (λ _ → idp)

{- A product Πᴳ indexed by Bool is the same as a binary product -}
-- XXX Get rid of [Lift] here.
module _ {i} (Pick : Lift {j = i} Bool → Group i) where

  Πᴳ-Bool-iso-×ᴳ :
    Πᴳ (Lift Bool) Pick ≃ᴳ (Pick (lift true)) ×ᴳ (Pick (lift false))
  Πᴳ-Bool-iso-×ᴳ = φ , e
    where
    φ = ×ᴳ-fanout (Πᴳ-proj {F = Pick} (lift true))
                  (Πᴳ-proj {F = Pick} (lift false))

    e : is-equiv (GroupHom.f φ)
    e = is-eq _ (λ {(g , h) → λ {(lift true) → g; (lift false) → h}})
          (λ _ → idp)
          (λ _ → λ= (λ {(lift true) → idp; (lift false) → idp}))

{- Commutativity of ×ᴳ -}
×ᴳ-comm : ∀ {i j} (H : Group i) (K : Group j) → H ×ᴳ K ≃ᴳ K ×ᴳ H
×ᴳ-comm H K =
  group-hom (λ {(h , k) → (k , h)}) (λ _ _ → idp) ,
  is-eq _ (λ {(k , h) → (h , k)}) (λ _ → idp) (λ _ → idp)

{- Associativity of ×ᴳ -}
×ᴳ-assoc : ∀ {i j k} (G : Group i) (H : Group j) (K : Group k)
  → ((G ×ᴳ H) ×ᴳ K) ≃ᴳ (G ×ᴳ (H ×ᴳ K))
×ᴳ-assoc G H K =
  group-hom (λ {((g , h) , k) → (g , (h , k))}) (λ _ _ → idp) ,
  is-eq _ (λ {(g , (h , k)) → ((g , h) , k)}) (λ _ → idp) (λ _ → idp)

module _ {i} where

  infixl 80 _^ᴳ_
  _^ᴳ_ : Group i → ℕ → Group i
  H ^ᴳ O = Lift-group {j = i} 0ᴳ
  H ^ᴳ (S n) = H ×ᴳ (H ^ᴳ n)

  ^ᴳ-+ : (H : Group i) (m n : ℕ) → H ^ᴳ (m + n) ≃ᴳ (H ^ᴳ m) ×ᴳ (H ^ᴳ n)
  ^ᴳ-+ H O n = ×ᴳ-emap (lift-iso {G = 0ᴳ}) (idiso (H ^ᴳ n)) ∘eᴳ ×ᴳ-unit-l (H ^ᴳ n) ⁻¹ᴳ
  ^ᴳ-+ H (S m) n = ×ᴳ-assoc H (H ^ᴳ m) (H ^ᴳ n) ⁻¹ᴳ ∘eᴳ ×ᴳ-emap (idiso H) (^ᴳ-+ H m n)

module _ where
  Πᴳ-is-trivial : ∀ {i j} (I : Type i) (F : I → Group j)
    → (∀ (i : I) → is-trivialᴳ (F i)) → is-trivialᴳ (Πᴳ I F)
  Πᴳ-is-trivial I F F-is-trivial = λ f → λ= λ i → F-is-trivial i (f i)
