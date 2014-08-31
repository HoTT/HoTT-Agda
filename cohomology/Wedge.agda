{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.FunctionOver
open import cohomology.OrdinaryTheory

{- Finite additivity is provable (and in a stronger form) without using
 - the additivity axiom. Cₙ(X ∨ Y) == Cₙ(X) × Cₙ(Y), and over this path
 -   ∙ Cₙ(winl) corresponds to fst : Cₙ(X) × Cₙ(Y) → Cₙ(X)
 -   ∙ Cₙ(winr) corresponds to snd : Cₙ(X) × Cₙ(Y) → Cₙ(Y)
 -   ∙ Cₙ(Wedge-rec winl* winr* wglue*) : Cₙ(Z) → Cₙ(X ∨ Y) corresponds to
       (λ cz → Cₙ(winl*) cz , Cₙ(winr*) cz)
 -}

module cohomology.Wedge {i} (OT : OrdinaryTheory i) (n : ℤ) {X Y : Ptd i} where

open import cohomology.WedgeCofiber {X = X} {Y = Y}

open OrdinaryTheory OT
open import cohomology.ConstantFunction OT

cprojl : GroupHom (C n (Ptd-Wedge X Y)) (C n X)
cprojl = CF-hom n ptd-winl

cprojr : GroupHom (C n (Ptd-Wedge X Y)) (C n Y)
cprojr = CF-hom n ptd-winr

cproj : GroupHom (C n (Ptd-Wedge X Y)) (C n X ×G C n Y)
cproj = ×-hom cprojl cprojr


cinl : GroupHom (C n X) (C n (Ptd-Wedge X Y))
cinl = CF-hom n ptd-projl

cinr : GroupHom (C n Y) (C n (Ptd-Wedge X Y))
cinr = CF-hom n ptd-projr

cin : GroupHom (C n X ×G C n Y) (C n (Ptd-Wedge X Y))
cin = ×-sum-hom (C-abelian n (Ptd-Wedge X Y)) cinl cinr

private
  module CX = Group (C n X)
  module CY = Group (C n Y)
  module CW = Group (C n (Ptd-Wedge X Y))

  module Cinl = GroupHom cinl
  module Cinr = GroupHom cinr
  module Cin = GroupHom cin

  module Cprojl = GroupHom cprojl
  module Cprojr = GroupHom cprojr
  module Cproj = GroupHom cproj


ptd-projl-winr : ptd-projl ∘ptd ptd-winr == ptd-cst
ptd-projl-winr = ptd-λ= (λ _ → idp) $
  ∙-unit-r _ ∙ ap-! projl wglue ∙ ap ! Projl.glue-β

ptd-projr-winr : ptd-projr ∘ptd ptd-winr == ptd-idf _
ptd-projr-winr = ptd-λ= (λ _ → idp) $
  ∙-unit-r _ ∙ ap-! projr wglue ∙ ap ! Projr.glue-β


cprojl-cinl : cprojl ∘hom cinl == idhom _
cprojl-cinl = ! (CF-comp n ptd-projl ptd-winl) ∙ CF-ident n

cprojr-cinl : cprojr ∘hom cinl == cst-hom
cprojr-cinl = ! (CF-comp n ptd-projl ptd-winr)
              ∙ ap (CF-hom n) ptd-projl-winr ∙ CF-cst n

cprojl-cinr : cprojl ∘hom cinr == cst-hom
cprojl-cinr = ! (CF-comp n ptd-projr ptd-winl) ∙ CF-cst n

cprojr-cinr : cprojr ∘hom cinr == idhom _
cprojr-cinr = ! (CF-comp n ptd-projr ptd-winr)
              ∙ ap (CF-hom n) ptd-projr-winr ∙ CF-ident n

cprojl-cin : (cx : CEl n X) (cy : CEl n Y)
  → Cprojl.f (CW.comp (Cinl.f cx) (Cinr.f cy)) == cx
cprojl-cin cx cy =
  Cprojl.f (CW.comp (Cinl.f cx) (Cinr.f cy))
    =⟨ Cprojl.pres-comp (Cinl.f cx) (Cinr.f cy) ⟩
  CX.comp (Cprojl.f (Cinl.f cx)) (Cprojl.f (Cinr.f cy))
    =⟨ ap2 CX.comp (app= (ap GroupHom.f cprojl-cinl) cx)
                   (app= (ap GroupHom.f cprojl-cinr) cy) ⟩
  CX.comp cx (Cid n X)
    =⟨ CX.unitr cx ⟩
  cx ∎

cprojr-cin : (cx : CEl n X) (cy : CEl n Y)
  → Cprojr.f (CW.comp (Cinl.f cx) (Cinr.f cy)) == cy
cprojr-cin cx cy =
  Cprojr.f (CW.comp (Cinl.f cx) (Cinr.f cy))
    =⟨ Cprojr.pres-comp (Cinl.f cx) (Cinr.f cy) ⟩
  CY.comp (Cprojr.f (Cinl.f cx)) (Cprojr.f (Cinr.f cy))
    =⟨ ap2 CY.comp (app= (ap GroupHom.f cprojr-cinl) cx)
                   (app= (ap GroupHom.f cprojr-cinr) cy) ⟩
  CY.comp (Cid n Y) cy
    =⟨ CY.unitl cy ⟩
  cy ∎

cproj-cin : (cxy : CEl n X × CEl n Y) → Cproj.f (Cin.f cxy) == cxy
cproj-cin (cx , cy) = pair×= (cprojl-cin cx cy) (cprojr-cin cx cy)


cproj-injective : (cw : CEl n (Ptd-Wedge X Y))
  → Cproj.f cw == (Cid n X , Cid n Y)
  → cw == Cid n (Ptd-Wedge X Y)
cproj-injective cw p =
  Trunc-rec (CW.El-level _ _)
    (λ {(cx , r) → lemma₂ cw cx r (fst×= p)})
    lemma₁
  where
  lemma₁ : Trunc ⟨-1⟩ (Σ (CEl n X) (λ cx → Cinl.f cx == cw))
  lemma₁ = ktoi
    (transport (λ {(_ , g) → is-exact (CF n g) (CF n ptd-winr)})
      (pair= CofWinr.ptd-path CofWinr.cfcod-over)
      (C-exact n ptd-winr))
    cw (snd×= p)

  lemma₂ : (cw' : CEl n (Ptd-Wedge X Y)) (cx : CEl n X)
    → Cinl.f cx == cw' → Cprojl.f cw' == Cid n X
    → cw' == Cid n (Ptd-Wedge X Y)
  lemma₂ ._ cx idp q =
    ap Cinl.f (! (app= (ap GroupHom.f cprojl-cinl) cx) ∙ q) ∙ Cinl.pres-ident


C-Wedge : C n (Ptd-Wedge X Y) == C n X ×G C n Y
C-Wedge = surj-inj-iso cproj
  (zero-kernel-injective cproj cproj-injective)
  (λ cxy → [ Cin.f cxy , cproj-cin cxy ])

CF-winl : CF-hom n ptd-winl == ×G-fst
          [ (λ K → GroupHom K (C n X)) ↓ C-Wedge ]
CF-winl = domain-over-iso _ _ _ _ $ domain-over-equiv fst _

CF-winr : CF-hom n ptd-winr == ×G-snd {G = C n X}
          [ (λ K → GroupHom K (C n Y)) ↓ C-Wedge ]
CF-winr = domain-over-iso _ _ _ _ $ domain-over-equiv snd _

CF-Wedge-rec : {Z : Ptd i} (winl* : fst X → fst Z) (winr* : fst Y → fst Z)
  (wglue* : winl* (snd X) == winr* (snd Y)) (pt : winl* (snd X) == snd Z)
  → CF-hom n (WedgeRec.f winl* winr* wglue* , pt)
    == ×-hom (CF-hom n (winl* , pt)) (CF-hom n (winr* , ! wglue* ∙ pt))
    [ (λ K → GroupHom (C n Z) K) ↓ C-Wedge ]
CF-Wedge-rec {Z = Z} winl* winr* wglue* pt =
  codomain-over-iso _ _ _ _ $
    codomain-over-equiv (fst (CF n (rec , pt))) _
    ▹ ap2 (λ f g z → (f z , g z))
        (ap GroupHom.f $ ! (CF-comp n (rec , pt) ptd-winl))
        (ap GroupHom.f $ ! (CF-comp n (rec , pt) ptd-winr)
                         ∙ ap (CF-hom n) (pair= idp pt-lemma))
  where
  rec = WedgeRec.f winl* winr* wglue*

  pt-lemma : ap rec (! wglue) ∙ pt == ! wglue* ∙ pt
  pt-lemma = ap (λ w → w ∙ pt) $
               ap-! rec wglue ∙ ap ! (WedgeRec.glue-β winl* winr* wglue*)

