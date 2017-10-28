{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Group
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Coproduct
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
×-group-struct {A = A} {B = B} GS HS = record {M} where
  module G = GroupStructure GS
  module H = GroupStructure HS
  module M where
    ident : A × B
    ident = G.ident , H.ident

    inv : A × B → A × B
    inv (g , h) = G.inv g , H.inv h

    comp : A × B → A × B → A × B
    comp (g₁ , h₁) (g₂ , h₂) = G.comp g₁ g₂ , H.comp h₁ h₂

    abstract
      unit-l : ∀ ab → comp ident ab == ab
      unit-l (g , h) = pair×= (G.unit-l g) (H.unit-l h)

      assoc : ∀ ab₁ ab₂ ab₃ → comp (comp ab₁ ab₂) ab₃ == comp ab₁ (comp ab₂ ab₃)
      assoc (g₁ , h₁) (g₂ , h₂) (g₃ , h₃) =
        pair×= (G.assoc g₁ g₂ g₃) (H.assoc h₁ h₂ h₃)

      inv-l : ∀ ab → comp (inv ab) ab == ident
      inv-l (g , h) = pair×= (G.inv-l g) (H.inv-l h)

infix 80 _×ᴳ_
_×ᴳ_ : ∀ {i j} → Group i → Group j → Group (lmax i j)
_×ᴳ_ (group A A-struct) (group B B-struct) =
  group (A × B) (×-group-struct A-struct B-struct)


{- general product -}
Π-group-struct : ∀ {i j} {I : Type i} {A : I → Type j}
  (FS : (i : I) → GroupStructure (A i))
  → GroupStructure (Π I A)
Π-group-struct FS = record {
  ident = ident ∘ FS;
  inv = λ f i → inv (FS i) (f i);
  comp = λ f g i → comp (FS i) (f i) (g i);
  unit-l = λ f → (λ= (λ i → unit-l (FS i) (f i)));
  assoc = λ f g h → (λ= (λ i → assoc (FS i) (f i) (g i) (h i)));
  inv-l = λ f → (λ= (λ i → inv-l (FS i) (f i)))}
  where open GroupStructure

Πᴳ : ∀ {i j} (I : Type i) (F : I → Group j) → Group (lmax i j)
Πᴳ I F = group (Π I (El ∘ F)) {{Π-level (λ i → El-level (F i))}} -- TODO: how to get instance search to work?
               (Π-group-struct (group-struct ∘ F))
  where open Group

{- functorial behavior of [Πᴳ] -}
Πᴳ-emap-r : ∀ {i j k} (I : Type i) {F : I → Group j} {G : I → Group k}
  → (∀ i → F i ≃ᴳ G i) → Πᴳ I F ≃ᴳ Πᴳ I G
Πᴳ-emap-r I {F} {G} iso = ≃-to-≃ᴳ (Π-emap-r (GroupIso.f-equiv ∘ iso))
  (λ f g → λ= λ i → GroupIso.pres-comp (iso i) (f i) (g i))

{- the product of abelian groups is abelian -}
×ᴳ-is-abelian : ∀ {i j} (G : Group i) (H : Group j)
  → is-abelian G → is-abelian H → is-abelian (G ×ᴳ H)
×ᴳ-is-abelian G H aG aH (g₁ , h₁) (g₂ , h₂) = pair×= (aG g₁ g₂) (aH h₁ h₂)

×ᴳ-abgroup : ∀ {i j} → AbGroup i → AbGroup j → AbGroup (lmax i j)
×ᴳ-abgroup (G , aG) (H , aH) = G ×ᴳ H , ×ᴳ-is-abelian G H aG aH

Πᴳ-is-abelian : ∀ {i j} {I : Type i} {F : I → Group j}
  → (∀ i → is-abelian (F i)) → is-abelian (Πᴳ I F)
Πᴳ-is-abelian aF f₁ f₂ = λ= (λ i → aF i (f₁ i) (f₂ i))

{- defining a homomorphism into a product -}
×ᴳ-fanout : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (G →ᴳ H) → (G →ᴳ K) → (G →ᴳ H ×ᴳ K)
×ᴳ-fanout (group-hom h h-comp) (group-hom k k-comp) =
  group-hom (fanout h k) (λ x y → pair×= (h-comp x y) (k-comp x y))

Πᴳ-fanout : ∀ {i j k} {I : Type i} {G : Group j} {F : I → Group k}
  → ((i : I) → G →ᴳ F i) → (G →ᴳ Πᴳ I F)
Πᴳ-fanout h = group-hom
  (λ x i → GroupHom.f (h i) x)
  (λ x y → λ= (λ i → GroupHom.pres-comp (h i) x y))

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
    module G = AbGroup (G , G-abelian)
    module H = Group H
    module K = Group K

  ×ᴳ-fanin : (H →ᴳ G) → (K →ᴳ G) → (H ×ᴳ K →ᴳ G)
  ×ᴳ-fanin φ ψ = group-hom (λ {(h , k) → G.comp (φ.f h) (ψ.f k)}) lemma
    where
      module φ = GroupHom φ
      module ψ = GroupHom ψ
      abstract
        lemma : preserves-comp (Group.comp (H ×ᴳ K)) G.comp
                  (λ {(h , k) → G.comp (φ.f h) (ψ.f k)})
        lemma (h₁ , k₁) (h₂ , k₂) =
          G.comp (φ.f (H.comp h₁ h₂)) (ψ.f (K.comp k₁ k₂))
            =⟨ φ.pres-comp h₁ h₂ |in-ctx (λ w → G.comp w (ψ.f (K.comp k₁ k₂))) ⟩
          G.comp (G.comp (φ.f h₁) (φ.f h₂)) (ψ.f (K.comp k₁ k₂))
            =⟨ ψ.pres-comp k₁ k₂
               |in-ctx (λ w → G.comp (G.comp (φ.f h₁) (φ.f h₂)) w)  ⟩
          G.comp (G.comp (φ.f h₁) (φ.f h₂)) (G.comp (ψ.f k₁) (ψ.f k₂))
            =⟨ G.interchange (φ.f h₁) (φ.f h₂) (ψ.f k₁) (ψ.f k₂) ⟩
          G.comp (G.comp (φ.f h₁) (ψ.f k₁)) (G.comp (φ.f h₂) (ψ.f k₂)) =∎

abstract
  ×ᴳ-fanin-η : ∀ {i j} (G : Group i) (H : Group j)
    (aGH : is-abelian (G ×ᴳ H))
    → ∀ gh → gh == GroupHom.f (×ᴳ-fanin {G = G ×ᴳ H} aGH ×ᴳ-inl ×ᴳ-inr) gh
  ×ᴳ-fanin-η G H aGH (g , h) =
    ! (pair×= (Group.unit-r G g) (Group.unit-l H h))

  ×ᴳ-fanin-pre∘ : ∀ {i j k l}
    {G : Group i} {H : Group j} {K : Group k} {L : Group l}
    (aK : is-abelian K) (aL : is-abelian L)
    (φ : K →ᴳ L) (ψ : G →ᴳ K) (χ : H →ᴳ K)
    → ∀ kh → GroupHom.f (×ᴳ-fanin aL (φ ∘ᴳ ψ) (φ ∘ᴳ χ)) kh
          == GroupHom.f (φ ∘ᴳ ×ᴳ-fanin aK ψ χ) kh
  ×ᴳ-fanin-pre∘ aK aL φ ψ χ (g , h) =
    ! (GroupHom.pres-comp φ (GroupHom.f ψ g) (GroupHom.f χ h))

{- define a homomorphism [G₁ × G₂ → H₁ × H₂] from homomorphisms
 - [G₁ → H₁] and [G₂ → H₂] -}
×ᴳ-fmap : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → (G₁ →ᴳ H₁) → (G₂ →ᴳ H₂) → (G₁ ×ᴳ G₂ →ᴳ H₁ ×ᴳ H₂)
×ᴳ-fmap {G₁ = G₁} {G₂} {H₁} {H₂} φ ψ = group-hom (×-fmap φ.f ψ.f) lemma
  where
    module φ = GroupHom φ
    module ψ = GroupHom ψ
    abstract
      lemma : preserves-comp (Group.comp (G₁ ×ᴳ G₂)) (Group.comp (H₁ ×ᴳ H₂))
                (λ {(h₁ , h₂) → (φ.f h₁ , ψ.f h₂)})
      lemma (h₁ , h₂) (h₁' , h₂') = pair×= (φ.pres-comp h₁ h₁') (ψ.pres-comp h₂ h₂')

×ᴳ-emap : ∀ {i j k l} {G₁ : Group i} {G₂ : Group j}
  {H₁ : Group k} {H₂ : Group l}
  → (G₁ ≃ᴳ H₁) → (G₂ ≃ᴳ H₂) → (G₁ ×ᴳ G₂ ≃ᴳ H₁ ×ᴳ H₂)
×ᴳ-emap (φ , φ-is-equiv) (ψ , ψ-is-equiv) =
  ×ᴳ-fmap φ ψ , ×-isemap φ-is-equiv ψ-is-equiv

{- equivalences in Πᴳ -}

Πᴳ-emap-l : ∀ {i j k} {A : Type i} {B : Type j} (F : B → Group k)
            → (e : A ≃ B) → Πᴳ A (F ∘ –> e) ≃ᴳ Πᴳ B F
Πᴳ-emap-l {A = A} {B = B} F e = ≃-to-≃ᴳ (Π-emap-l (Group.El ∘ F) e) lemma
  where abstract lemma = λ f g → λ= λ b → transp-El-pres-comp F (<–-inv-r e b) (f (<– e b)) (g (<– e b))

{- 0ᴳ is a unit for product -}
×ᴳ-unit-l : ∀ {i} (G : Group i) → 0ᴳ ×ᴳ G ≃ᴳ G
×ᴳ-unit-l _ = ×ᴳ-snd {G = 0ᴳ} , is-eq snd (λ g → (unit , g)) (λ _ → idp) (λ _ → idp)

×ᴳ-unit-r : ∀ {i} (G : Group i) → G ×ᴳ 0ᴳ ≃ᴳ G
×ᴳ-unit-r _ = ×ᴳ-fst , is-eq fst (λ g → (g , unit)) (λ _ → idp) (λ _ → idp)

{- A product Πᴳ indexed by Bool is the same as a binary product -}
module _ {i j k} {A : Type i} {B : Type j} (F : A ⊔ B → Group k) where

  Πᴳ₁-⊔-iso-×ᴳ : Πᴳ (A ⊔ B) F ≃ᴳ Πᴳ A (F ∘ inl) ×ᴳ Πᴳ B (F ∘ inr)
  Πᴳ₁-⊔-iso-×ᴳ = ≃-to-≃ᴳ (Π₁-⊔-equiv-× (Group.El ∘ F)) (λ _ _ → idp)

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

module _ {j} {F : Unit → Group j} where
  Πᴳ₁-Unit : Πᴳ Unit F ≃ᴳ F unit
  Πᴳ₁-Unit = ≃-to-≃ᴳ Π₁-Unit (λ _ _ → idp)
