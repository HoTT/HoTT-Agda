{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFlattening
open import lib.types.PushoutFmap
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Unit

-- Wedge of two pointed types is defined as a particular case of pushout

module lib.types.Wedge where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙∨-span : ⊙Span
  ⊙∨-span = ⊙span X Y ⊙Unit ⊙cst ⊙cst
  ⊙wedge-span = ⊙∨-span

  ∨-span : Span
  ∨-span = ⊙Span-to-Span ⊙∨-span
  wedge-span = ∨-span

  Wedge : Type (lmax i j)
  Wedge = Pushout wedge-span

  infix 80 _∨_
  _∨_ = Wedge

  ⊙Wedge : Ptd (lmax i j)
  ⊙Wedge = ⊙Pushout ⊙wedge-span

  infix 80 _⊙∨_
  _⊙∨_ = ⊙Wedge

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  winl : de⊙ X → X ∨ Y
  winl x = left x

  winr : de⊙ Y → X ∨ Y
  winr y = right y

  wglue : winl (pt X) == winr (pt Y)
  wglue = glue tt

  ⊙winl : X ⊙→ X ⊙∨ Y
  ⊙winl = (winl , idp)

  ⊙winr : Y ⊙→ X ⊙∨ Y
  ⊙winr = (winr , ! wglue)

  module WedgeElim {k} {P : X ∨ Y → Type k}
    (winl* : (x : de⊙ X) → P (winl x)) (winr* : (y : de⊙ Y) → P (winr y))
    (glue* : winl* (pt X) == winr* (pt Y) [ P ↓ wglue ]) where

    private
      module M = PushoutElim winl* winr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  ∨-elim = WedgeElim.f
  Wedge-elim = WedgeElim.f

  module WedgeRec {k} {C : Type k} (winl* : de⊙ X → C) (winr* : de⊙ Y → C)
    (glue* : winl* (pt X) == winr* (pt Y)) where

    private
      module M = PushoutRec {d = wedge-span X Y} winl* winr* (λ _ → glue*)

    f = M.f
    glue-β = M.glue-β unit

  ∨-rec = WedgeRec.f
  Wedge-rec = WedgeRec.f

  module ⊙WedgeRec {k} {Z : Ptd k} (g : X ⊙→ Z) (h : Y ⊙→ Z) where

    open WedgeRec (fst g) (fst h) (snd g ∙ ! (snd h)) public

    ⊙f : X ⊙∨ Y ⊙→ Z
    ⊙f = (f , snd g)

    ⊙winl-β : ⊙f ⊙∘ ⊙winl == g
    ⊙winl-β = idp

    ⊙winr-β : ⊙f ⊙∘ ⊙winr == h
    ⊙winr-β = ⊙λ=' (λ _ → idp) lemma where
      abstract
        lemma : snd (⊙f ⊙∘ ⊙winr) == snd h
        lemma =
          ap (_∙ snd g)
             (ap-! f wglue ∙ ap ! glue-β ∙ !-∙ (snd g) (! (snd h)))
          ∙ ∙-assoc (! (! (snd h))) (! (snd g)) (snd g)
          ∙ ap (! (! (snd h)) ∙_) (!-inv-l (snd g))
          ∙ ∙-unit-r (! (! (snd h)))
          ∙ !-! (snd h)

  ⊙∨-rec = ⊙WedgeRec.⊙f
  ⊙Wedge-rec = ⊙WedgeRec.⊙f

  ⊙Wedge-rec-post∘ : ∀ {k l} {Z : Ptd k} {W : Ptd l}
    (k : Z ⊙→ W) (g : X ⊙→ Z) (h : Y ⊙→ Z)
    → k ⊙∘ ⊙Wedge-rec g h ⊙∼ ⊙Wedge-rec (k ⊙∘ g) (k ⊙∘ h)
  ⊙Wedge-rec-post∘ k g h =
    (Wedge-elim (λ _ → idp) (λ _ → idp)
      (↓-='-in' $ ⊙WedgeRec.glue-β (k ⊙∘ g) (k ⊙∘ h)
                 ∙ lemma (fst k) (snd g) (snd h) (snd k)
                 ∙ ! (ap (ap (fst k)) (⊙WedgeRec.glue-β g h))
                 ∙ ∘-ap (fst k) (fst (⊙Wedge-rec g h)) wglue)) ,
    idp
    where
    lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} {w : B}
      (p : x == z) (q : y == z) (r : f z == w)
      → (ap f p ∙ r) ∙ ! (ap f q ∙ r) == ap f (p ∙ ! q)
    lemma f idp idp idp = idp
  ⊙∨-rec-post∘ = ⊙Wedge-rec-post∘

  ⊙Wedge-rec-η : ⊙Wedge-rec ⊙winl ⊙winr == ⊙idf (X ⊙∨ Y)
  ⊙Wedge-rec-η = ⊙λ='
    (Wedge-elim (λ _ → idp) (λ _ → idp)
      (↓-='-in' $ ap-idf wglue
                 ∙ ! (!-! wglue)
                 ∙ ! (⊙WedgeRec.glue-β ⊙winl ⊙winr)))
    idp
  ⊙∨-rec-η = ⊙Wedge-rec-η

  add-wglue : de⊙ (X ⊙⊔ Y) → X ∨ Y
  add-wglue (inl x) = winl x
  add-wglue (inr y) = winr y

  ⊙add-wglue : X ⊙⊔ Y ⊙→ X ⊙∨ Y
  ⊙add-wglue = add-wglue , idp

  module Projl = ⊙WedgeRec (⊙idf X) (⊙cst {X = Y})
  module Projr = ⊙WedgeRec (⊙cst {X = X}) (⊙idf Y)

  projl = Projl.f
  projr = Projr.f
  ⊙projl = Projl.⊙f
  ⊙projr = Projr.⊙f

  module WedgeToProduct = ⊙WedgeRec ((_, pt Y) , idp) ((pt X ,_), idp)

  ∨-⊙to-× : X ⊙∨ Y ⊙→ X ⊙× Y
  ∨-⊙to-× = WedgeToProduct.⊙f

  ∨-to-× : X ∨ Y → de⊙ (X ⊙× Y)
  ∨-to-× = WedgeToProduct.f

  ∨-to-×-glue-β : ap ∨-to-× wglue == idp
  ∨-to-×-glue-β = WedgeToProduct.glue-β
    
  abstract
    ↓-∨to×=cst-in : ∀ {x y} {p p' : (pt X , pt Y) == (x , y)}
      → p == p'
      → p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ]
    ↓-∨to×=cst-in {p' = idp} q =
      ↓-app=cst-in' (q ∙ ! WedgeToProduct.glue-β)

    ↓-∨to×=cst-out : ∀ {x y} {p p' : (pt X , pt Y) == (x , y)}
      → p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ]
      → p == p'
    ↓-∨to×=cst-out {p' = idp} q =
      ↓-app=cst-out' q ∙ WedgeToProduct.glue-β

    ↓-∨to×=cst-β : ∀ {x y} {p p' : (pt X , pt Y) == (x , y)}
      (q : p == p')
      → ↓-∨to×=cst-out (↓-∨to×=cst-in q) == q
    ↓-∨to×=cst-β {p' = idp} idp =
        ap (_∙ WedgeToProduct.glue-β) (↓-app=cst-β' {p = wglue} (! WedgeToProduct.glue-β))
      ∙ !-inv-l WedgeToProduct.glue-β

    ↓-∨to×=cst-η : ∀ {x y} {p p' : (pt X , pt Y) == (x , y)}
      (q : p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ])
      → ↓-∨to×=cst-in (↓-∨to×=cst-out q) == q
    ↓-∨to×=cst-η {p = p} {p' = idp} q =
        ap ↓-app=cst-in'
          ( ∙-assoc (↓-app=cst-out' q) WedgeToProduct.glue-β (! WedgeToProduct.glue-β)
          ∙ ap (↓-app=cst-out' q ∙_) (!-inv-r WedgeToProduct.glue-β)
          ∙ ∙-unit-r (↓-app=cst-out' q))
      ∙ ↓-app=cst-η' q

module Fold {i} {X : Ptd i} = ⊙WedgeRec (⊙idf X) (⊙idf X)
fold = Fold.f
⊙fold = Fold.⊙f

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  (fX : X ⊙→ X') (fY : Y ⊙→ Y') where

  wedge-span-map : SpanMap (wedge-span X Y) (wedge-span X' Y')
  wedge-span-map = span-map (fst fX) (fst fY) (idf _)
                      (comm-sqr λ _ → snd fX)
                      (comm-sqr λ _ → snd fY)

  module WedgeFmap where
    private
      module M = PushoutFmap wedge-span-map
    f = M.f
    glue-β = M.glue-β unit

  ∨-fmap : X ∨ Y → X' ∨ Y'
  ∨-fmap = WedgeFmap.f

  ⊙∨-fmap : X ⊙∨ Y ⊙→ X' ⊙∨ Y'
  ⊙∨-fmap = ∨-fmap , ap winl (snd fX)

  Wedge-fmap = ∨-fmap
  ⊙Wedge-fmap = ⊙∨-fmap

module _ {i₀ i₁ i₂ j₀ j₁ j₂} {X₀ : Ptd i₀} {X₁ : Ptd i₁} {X₂ : Ptd i₂}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂}
  where

  ∨-fmap-∘ :
    (gX : X₁ ⊙→ X₂) (fX : X₀ ⊙→ X₁)
    (gY : Y₁ ⊙→ Y₂) (fY : Y₀ ⊙→ Y₁)
    → ∨-fmap (gX ⊙∘ fX) (gY ⊙∘ fY) ∼ ∨-fmap gX gY ∘ ∨-fmap fX fY
  ∨-fmap-∘ (gX , idp) (fX , idp) (gY , idp) (fY , idp) =
    Pushout-fmap-∘ (wedge-span-map (gX , idp) (gY , idp)) (wedge-span-map (fX , idp) (fY , idp))

  ⊙∨-fmap-∘ :
    (gX : X₁ ⊙→ X₂) (fX : X₀ ⊙→ X₁)
    (gY : Y₁ ⊙→ Y₂) (fY : Y₀ ⊙→ Y₁)
    → ⊙∨-fmap (gX ⊙∘ fX) (gY ⊙∘ fY) ⊙∼ ⊙∨-fmap gX gY ⊙∘ ⊙∨-fmap fX fY
  ⊙∨-fmap-∘ (gX , idp) (fX , idp) (gY , idp) (fY , idp) =
    ∨-fmap-∘ (gX , idp) (fX , idp) (gY , idp) (fY , idp) , idp

  Wedge-fmap-∘ = ∨-fmap-∘
  ⊙Wedge-fmap-∘ = ⊙∨-fmap-∘

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  (eqX : X ⊙≃ X') (eqY : Y ⊙≃ Y') where

  wedge-span-emap : SpanEquiv (wedge-span X Y) (wedge-span X' Y')
  wedge-span-emap = wedge-span-map (⊙–> eqX) (⊙–> eqY)
                  , snd eqX , snd eqY , idf-is-equiv _

  ∨-emap : X ∨ Y ≃ X' ∨ Y'
  ∨-emap = Pushout-emap wedge-span-emap

  ⊙∨-emap : X ⊙∨ Y ⊙≃ X' ⊙∨ Y'
  ⊙∨-emap = ≃-to-⊙≃ ∨-emap (ap winl (⊙–>-pt eqX))

  Wedge-emap = ∨-emap
  ⊙Wedge-emap = ⊙∨-emap

module _ {i i' j j' k} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j}
  {Y' : Ptd j'} {Z : Ptd k} (winl* : X' ⊙→ Z) (winr* : Y' ⊙→ Z)
  (f : X ⊙→ X') (g : Y ⊙→ Y') where

  ⊙Wedge-rec-fmap :
       ⊙Wedge-rec winl* winr* ⊙∘ ⊙∨-fmap f g
    ⊙∼ ⊙Wedge-rec (winl* ⊙∘ f) (winr* ⊙∘ g)
  ⊙Wedge-rec-fmap =
    Wedge-elim (λ _ → idp) (λ _ → idp) (↓-='-in' $ ! $ lemma₀ winl* winr* f g) ,
    lemma₁ winl* winr* f
    where
      abstract
        lemma₀ : ∀ {X' Y' Z} (winl* : X' ⊙→ Z) (winr* : Y' ⊙→ Z)
          (f : X ⊙→ X') (g : Y ⊙→ Y')
          →  ap (⊙WedgeRec.f winl* winr* ∘ ∨-fmap f g) wglue
          == ap (⊙WedgeRec.f (winl* ⊙∘ f) (winr* ⊙∘ g)) wglue
        lemma₀ (winl* , idp) (winr* , winr*-pt) (f , idp) (g , idp) =
          ap (Wedge-rec winl* winr* (! winr*-pt) ∘ ∨-fmap (f , idp) (g , idp)) wglue
            =⟨ ap-∘ (Wedge-rec winl* winr* (! winr*-pt)) (∨-fmap (f , idp) (g , idp)) wglue ⟩
          ap (Wedge-rec winl* winr* (! winr*-pt)) (ap (∨-fmap (f , idp) (g , idp)) wglue)
            =⟨ ap (ap (Wedge-rec winl* winr* (! winr*-pt))) $ WedgeFmap.glue-β (f , idp) (g , idp) ⟩
          ap (Wedge-rec winl* winr* (! winr*-pt)) wglue
            =⟨ WedgeRec.glue-β winl* winr* (! winr*-pt) ⟩
          ! winr*-pt
            =⟨ ! $ WedgeRec.glue-β (winl* ∘ f) (winr* ∘ g) (! winr*-pt) ⟩
          ap (Wedge-rec (winl* ∘ f) (winr* ∘ g) (! winr*-pt)) wglue
            =∎

        lemma₁ : ∀ {X' Z} (winl* : X' ⊙→ Z) (winr* : Y' ⊙→ Z) (f : X ⊙→ X')
          →  snd (⊙Wedge-rec winl* winr* ⊙∘ ⊙∨-fmap f g)
          == snd (⊙Wedge-rec (winl* ⊙∘ f) (winr* ⊙∘ g))
        lemma₁ (f , idp) _ (winl* , idp) = idp
  ⊙∨-rec-fmap = ⊙Wedge-rec-fmap

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j}
  {Y' : Ptd j'} (f : X ⊙→ X') (g : Y ⊙→ Y') where

  ⊙projl-fmap : ⊙projl ⊙∘ ⊙∨-fmap f g ⊙∼ ⊙Wedge-rec f ⊙cst
  ⊙projl-fmap =
    Wedge-elim (λ _ → idp) (λ _ → idp) (↓-='-in' $ ! $ lemma₀ f g) , lemma₁ f g
    where
      abstract
        lemma₀ : ∀ {X' Y'} (f : X ⊙→ X') (g : Y ⊙→ Y')
          →  ap (projl ∘ ∨-fmap f g) wglue
          == ap (⊙WedgeRec.f f ⊙cst) wglue
        lemma₀ (f , idp) (g , idp) =
          ap (projl ∘ ∨-fmap (f , idp) (g , idp)) wglue
            =⟨ ap-∘ projl (∨-fmap (f , idp) (g , idp)) wglue ⟩
          ap projl (ap (∨-fmap (f , idp) (g , idp)) wglue)
            =⟨ ap (ap projl) (WedgeFmap.glue-β (f , idp) (g , idp)) ⟩
          ap projl wglue
            =⟨ Projl.glue-β ⟩
          idp
            =⟨ ! $ ⊙WedgeRec.glue-β (f , idp) ⊙cst ⟩
          ap (⊙WedgeRec.f (f , idp) ⊙cst) wglue
            =∎

        lemma₁ : ∀ {X' Y'} (f : X ⊙→ X') (g : Y ⊙→ Y')
          →  snd (⊙projl ⊙∘ ⊙∨-fmap f g)
          == snd (⊙Wedge-rec {Y = Y} f ⊙cst)
        lemma₁ (f , idp) (g , idp) = idp

  ⊙projr-fmap : ⊙projr ⊙∘ ⊙∨-fmap f g ⊙∼ ⊙Wedge-rec ⊙cst g
  ⊙projr-fmap =
    Wedge-elim (λ _ → idp) (λ _ → idp) (↓-='-in' $ ! $ lemma₀ f g) , lemma₁ f g
    where
      abstract
        lemma₀ : ∀ {X' Y'} (f : X ⊙→ X') (g : Y ⊙→ Y')
          →  ap (projr ∘ ∨-fmap f g) wglue
          == ap (⊙WedgeRec.f ⊙cst g) wglue
        lemma₀ (f , idp) (g , idp) =
          ap (projr ∘ ∨-fmap (f , idp) (g , idp)) wglue
            =⟨ ap-∘ projr (∨-fmap (f , idp) (g , idp)) wglue ⟩
          ap projr (ap (∨-fmap (f , idp) (g , idp)) wglue)
            =⟨ ap (ap projr) (WedgeFmap.glue-β (f , idp) (g , idp)) ⟩
          ap projr wglue
            =⟨ Projr.glue-β ⟩
          idp
            =⟨ ! $ ⊙WedgeRec.glue-β ⊙cst (g , idp) ⟩
          ap (⊙WedgeRec.f ⊙cst (g , idp)) wglue
            =∎

        lemma₁ : ∀ {X' Y'} (f : X ⊙→ X') (g : Y ⊙→ Y')
          →  snd (⊙projr ⊙∘ ⊙∨-fmap f g)
          == snd (⊙Wedge-rec {X = X} ⊙cst g)
        lemma₁ (f , idp) (g , idp) = idp

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Z) (g : Y ⊙→ Z) where

  {- favonia: This is a special case, but still proved separately to make sure
     it has good computational content. (Maybe this is overkilling.) -}
  ⊙fold-fmap : ⊙fold ⊙∘ ⊙∨-fmap f g ⊙∼ ⊙Wedge-rec f g
  ⊙fold-fmap =
    Wedge-elim (λ _ → idp) (λ _ → idp) (↓-='-in' $ ! $ lemma₀ f g) , lemma₁ f g
    where
      abstract
        lemma₀ : ∀ {Z} (f : X ⊙→ Z) (g : Y ⊙→ Z)
          →  ap (⊙WedgeRec.f (⊙idf _) (⊙idf _) ∘ ∨-fmap f g) wglue
          == ap (⊙WedgeRec.f f g) wglue
        lemma₀ (f , idp) (g , g-pt) =
          ap (⊙WedgeRec.f (⊙idf _) (⊙idf _) ∘ ∨-fmap (f , idp) (g , g-pt)) wglue
            =⟨ ap-∘
                (⊙WedgeRec.f (⊙idf _) (⊙idf _))
                (∨-fmap (f , idp) (g , g-pt))
                wglue ⟩
          ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)) (ap (∨-fmap (f , idp) (g , g-pt)) wglue)
            =⟨ ap (ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)))
                  (WedgeFmap.glue-β (f , idp) (g , g-pt)) ⟩
          ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)) (wglue ∙' ap winr (! g-pt))
            =⟨ ap-∙' (⊙WedgeRec.f (⊙idf _) (⊙idf _)) wglue (ap winr (! g-pt)) ⟩
          ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)) wglue
            ∙' ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)) (ap winr (! g-pt))
            =⟨ ap2 _∙'_
                (⊙WedgeRec.glue-β (⊙idf _) (⊙idf _))
                ( ∘-ap (⊙WedgeRec.f (⊙idf _) (⊙idf _)) winr (! g-pt)
                ∙ ap-idf (! g-pt)) ⟩
          idp ∙' ! g-pt
            =⟨ ∙'-unit-l (! g-pt) ⟩
          ! g-pt
            =⟨ ! $ ⊙WedgeRec.glue-β (f , idp) (g , g-pt) ⟩
          ap (⊙WedgeRec.f (f , idp) (g , g-pt) ) wglue
            =∎

        lemma₁ : ∀ {Z} (f : X ⊙→ Z) (g : Y ⊙→ Z)
          →  snd (⊙Wedge-rec (⊙idf _) (⊙idf _) ⊙∘ ⊙∨-fmap f g)
          == snd (⊙Wedge-rec f g)
        lemma₁ (f , idp) (g , g-pt) = idp

module _ {i j k} (X : Ptd i) (Y : Ptd j) (Z : Ptd k) where
    
  module WedgeAssocInl = WedgeRec {C = X ∨ (Y ⊙∨ Z)} winl (winr ∘ winl) wglue
  module WedgeAssoc = WedgeRec {X = X ⊙∨ Y} WedgeAssocInl.f (winr ∘ winr) (wglue ∙ ap winr wglue)

  ∨-assoc : (X ⊙∨ Y) ∨ Z ≃ X ∨ (Y ⊙∨ Z)
  ∨-assoc = equiv to from to-from from-to where

    to : (X ⊙∨ Y) ∨ Z → X ∨ (Y ⊙∨ Z)
    to = WedgeAssoc.f

    module FromInr = WedgeRec {C = (X ⊙∨ Y) ∨ Z} (winl ∘ winr) winr (! (ap winl wglue) ∙ wglue)
    module From = WedgeRec {Y = Y ⊙∨ Z} (winl ∘ winl) FromInr.f (ap winl wglue)

    from : X ∨ (Y ⊙∨ Z) → (X ⊙∨ Y) ∨ Z
    from = From.f

    abstract
      to-from : ∀ x → to (from x) == x
      to-from = Wedge-elim
        (λ x → idp)
        (Wedge-elim (λ y → idp) (λ z → idp) $ ↓-='-in' $ ! $
          ap (to ∘ FromInr.f) wglue
            =⟨ ap-∘ to FromInr.f wglue ⟩
          ap to (ap FromInr.f wglue)
            =⟨ ap (ap to) FromInr.glue-β ⟩
          ap to (! (ap winl wglue) ∙ wglue)
            =⟨ ap-∙ to (! (ap winl wglue)) wglue ⟩
          ap to (! (ap winl wglue)) ∙ ap to wglue
            =⟨ _∙2_ (ap-! to (ap winl wglue) ∙ ap ! (∘-ap to winl wglue ∙ WedgeAssocInl.glue-β)) WedgeAssoc.glue-β ⟩
          ! wglue ∙ wglue ∙ ap winr wglue
            =⟨ ! $ ∙-assoc (! wglue) wglue (ap winr wglue) ⟩
          (! wglue ∙ wglue) ∙ ap winr wglue
            =⟨ ap (_∙ ap winr wglue) (!-inv-l wglue) ⟩
          ap winr wglue
            =∎)
        (↓-∘=idf-in' to from {p = wglue} (ap (ap to) From.glue-β ∙ ∘-ap to winl wglue ∙ WedgeAssocInl.glue-β))

      from-to : ∀ x → from (to x) == x
      from-to = Wedge-elim
        (Wedge-elim (λ x → idp) (λ y → idp) $ ↓-='-in' $ ! $
          ap-∘ from WedgeAssocInl.f wglue ∙ ap (ap from) WedgeAssocInl.glue-β ∙ From.glue-β)
        (λ z → idp)
        (↓-∘=idf-in' from to {p = wglue} $
          ap from (ap to wglue)
            =⟨ ap (ap from) WedgeAssoc.glue-β ⟩
          ap from (wglue ∙ ap winr wglue)
            =⟨ ap-∙ from wglue (ap winr wglue) ⟩
          ap from wglue ∙ ap from (ap winr wglue)
            =⟨ From.glue-β ∙2 (∘-ap from winr wglue ∙ FromInr.glue-β) ⟩
          ap winl wglue ∙ ! (ap winl wglue) ∙ wglue
            =⟨ ! $ ∙-assoc (ap winl wglue) (! (ap winl wglue)) wglue ⟩
          (ap winl wglue ∙ ! (ap winl wglue)) ∙ wglue
            =⟨ ap (_∙ wglue) (!-inv-r (ap winl wglue)) ⟩
          wglue
            =∎)

  ⊙∨-assoc : (X ⊙∨ Y) ⊙∨ Z ⊙≃ X ⊙∨ (Y ⊙∨ Z)
  ⊙∨-assoc = ≃-to-⊙≃ ∨-assoc idp

{-
module _ {i₀ i₁ j₀ j₁ k₀ k₁}
  {X₀ : Ptd i₀} {Y₀ : Ptd j₀} {Z₀ : Ptd k₀}
  {X₁ : Ptd i₁} {Y₁ : Ptd j₁} {Z₁ : Ptd k₁}
  where

  ⊙∨-assoc-nat : ∀ (f : X₀ ⊙→ X₁) (g : Y₀ ⊙→ Y₁) (h : Z₀ ⊙→ Z₁)
    →  ⊙–> (⊙∨-assoc X₁ Y₁ Z₁) ⊙∘ ⊙∨-fmap (⊙∨-fmap f g) h
    ⊙∼ ⊙∨-fmap f (⊙∨-fmap g h) ⊙∘ ⊙–> (⊙∨-assoc X₀ Y₀ Z₀)
  ⊙∨-assoc-nat (f , idp) (g , idp) (h , idp) =
    (Wedge-elim
      -- {P = –> (∨-assoc X₁ Y₁ Z₁) ∘ ∨-fmap (⊙∨-fmap f g) h ∼ ∨-fmap f (⊙∨-fmap g h) ∘ –> (∨-assoc X₀ Y₀ Z₀)}
      (Wedge-elim (λ _ → idp) (λ _ → idp)
        (↓-='-in' $
          ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp)) ∘ WedgeAssocInl.f X₀ Y₀ Z₀) wglue
            =⟨ ap-∘ (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (WedgeAssocInl.f X₀ Y₀ Z₀) wglue ⟩
          ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (ap (WedgeAssocInl.f X₀ Y₀ Z₀) wglue)
            =⟨ ap (ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp)))) (WedgeAssocInl.glue-β X₀ Y₀ Z₀) ⟩
          ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) wglue
            =⟨ WedgeFmap.glue-β (f , idp) (⊙∨-fmap (g , idp) (h , idp)) ⟩
          wglue
            =⟨ ! $ WedgeAssocInl.glue-β X₁ Y₁ Z₁ ⟩
          ap (WedgeAssocInl.f X₁ Y₁ Z₁) wglue
            =⟨ ! $ ap (ap (WedgeAssocInl.f X₁ Y₁ Z₁)) $ WedgeFmap.glue-β (f , idp) (g , idp) ⟩
          ap (WedgeAssocInl.f X₁ Y₁ Z₁) (ap (∨-fmap (f , idp) (g , idp)) wglue)
            =⟨ ∘-ap (WedgeAssocInl.f X₁ Y₁ Z₁) (∨-fmap (f , idp) (g , idp)) wglue ⟩
          ap (WedgeAssocInl.f X₁ Y₁ Z₁ ∘ ∨-fmap (f , idp) (g , idp)) wglue
            =∎))
      (λ _ → idp)
      (↓-='-in' $
        ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp)) ∘ WedgeAssoc.f X₀ Y₀ Z₀) wglue
          =⟨ ap-∘ (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (WedgeAssoc.f X₀ Y₀ Z₀) wglue ⟩
        ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (ap (WedgeAssoc.f X₀ Y₀ Z₀) wglue)
          =⟨ ap (ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp)))) (WedgeAssoc.glue-β X₀ Y₀ Z₀) ⟩
        ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (wglue ∙ ap winr wglue)
          =⟨ ap-∙ (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) wglue (ap winr wglue) ⟩
        ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) wglue
        ∙ ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) (ap winr wglue)
          =⟨ ap2 _∙_
               (WedgeFmap.glue-β (f , idp) (⊙∨-fmap (g , idp) (h , idp)))
               ( ∘-ap (∨-fmap (f , idp) (⊙∨-fmap (g , idp) (h , idp))) winr wglue
               ∙ ap-∘ winr (∨-fmap (g , idp) (h , idp)) wglue
               ∙ ap (ap winr) (WedgeFmap.glue-β (g , idp) (h , idp))) ⟩
        wglue ∙ ap winr wglue
          =⟨ ! $ WedgeAssoc.glue-β X₁ Y₁ Z₁ ⟩
        ap (WedgeAssoc.f X₁ Y₁ Z₁) wglue
          =⟨ ! $ ap (ap (WedgeAssoc.f X₁ Y₁ Z₁)) $ WedgeFmap.glue-β (⊙∨-fmap (f , idp) (g , idp)) (h , idp) ⟩
        ap (WedgeAssoc.f X₁ Y₁ Z₁) (ap (∨-fmap (⊙∨-fmap (f , idp) (g , idp)) (h , idp)) wglue)
          =⟨ ∘-ap (WedgeAssoc.f X₁ Y₁ Z₁) (∨-fmap (⊙∨-fmap (f , idp) (g , idp)) (h , idp)) wglue ⟩
        ap (WedgeAssoc.f X₁ Y₁ Z₁ ∘ ∨-fmap (⊙∨-fmap (f , idp) (g , idp)) (h , idp)) wglue
          =∎))
    ,
    idp
-}

module _ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : X ⊙→ W) (g : Y ⊙→ W) (h : Z ⊙→ W) where

  ⊙Wedge-rec-assoc : ⊙Wedge-rec (⊙Wedge-rec f g) h
    ⊙∼ ⊙Wedge-rec f (⊙Wedge-rec g h) ⊙∘ ⊙–> (⊙∨-assoc X Y Z)
  ⊙Wedge-rec-assoc =
    (Wedge-elim
      (Wedge-elim (λ x → idp) (λ y → idp)
        (↓-='-in' $
            ap-∘ (⊙WedgeRec.f f (⊙Wedge-rec g h)) (WedgeAssocInl.f X Y Z) wglue
          ∙ ap (ap (⊙WedgeRec.f f (⊙Wedge-rec g h))) (WedgeAssocInl.glue-β X Y Z)
          ∙ ⊙WedgeRec.glue-β f (⊙Wedge-rec g h)
          ∙ ! (⊙WedgeRec.glue-β f g)))
      (λ z → idp)
      (↓-='-in' $
          ap-∘ (⊙WedgeRec.f f (⊙Wedge-rec g h)) (WedgeAssoc.f X Y Z) wglue
        ∙ ap (ap (⊙WedgeRec.f f (⊙Wedge-rec g h))) (WedgeAssoc.glue-β X Y Z)
        ∙ ap-∙ (⊙WedgeRec.f f (⊙Wedge-rec g h)) wglue (ap winr wglue)
        ∙ _∙2_ (⊙WedgeRec.glue-β f (⊙Wedge-rec g h))
               ( ∘-ap (⊙WedgeRec.f f (⊙Wedge-rec g h)) winr wglue
               ∙ ⊙WedgeRec.glue-β g h)
        ∙ ∙-assoc (snd f) (! (snd g)) (snd g ∙ ! (snd h))
        ∙ ap (snd f ∙_) (! $ ∙-assoc (! (snd g)) (snd g) (! (snd h)))
        ∙ ap (λ p → snd f ∙ p ∙ ! (snd h)) (!-inv-l (snd g))
        ∙ ! (⊙WedgeRec.glue-β (⊙Wedge-rec f g) h)))
    ,
    idp
  ⊙∨-rec-assoc = ⊙Wedge-rec-assoc
