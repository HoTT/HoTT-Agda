{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- Useful lemmas for computing the effect of transporting a function
 - across an equivalence in the domain or codomain.
 - TODO move these lemmas into lib.types.Pi or lib.types.PointedPi -}

-- XXX Naming convensions?

module stash.homotopy.FunctionOver where

{- transporting a ptd function along a equivalence or path in the domain -}
module _ {i} {j} {Y : Ptd i} {Z : Ptd j} (g : Y ⊙→ Z) where

  domain-over-⊙path : {X : Ptd i} (p : de⊙ X == de⊙ Y)
    (q : coe p (pt X) == pt Y)
    → g ⊙∘ (coe p , q) == g [ (λ W → W ⊙→ Z) ↓ ptd= p (↓-idf-in p q) ]
  domain-over-⊙path idp idp = idp

  domain-over-⊙equiv : {X : Ptd i} (e : X ⊙≃ Y)
    → g ⊙∘ ⊙–> e == g [ (λ W → W ⊙→ Z) ↓ ⊙ua e ]
  domain-over-⊙equiv {X = X} e =
    ap (λ w → g ⊙∘ w) (! $ ⊙λ= (coe-β (⊙≃-to-≃ e)) (↓-idf=cst-in idp))
    ◃ domain-over-⊙path (ua (⊙≃-to-≃ e))
                        (coe-β (⊙≃-to-≃ e) (pt X) ∙ snd (⊙–> e))

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (f : X ⊙→ Z) where

  domain!-over-⊙path : {Y : Ptd i} (p : de⊙ X == de⊙ Y)
    (q : coe p (pt X) == pt Y)
    → f == f ⊙∘ (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (pt X))
      [ (λ W → W ⊙→ Z) ↓ ptd= p (↓-idf-in p q) ]
  domain!-over-⊙path idp idp = idp

  domain!-over-⊙equiv : {Y : Ptd i} (e : X ⊙≃ Y)
    → f == f ⊙∘ (⊙<– e) [ (λ W → W ⊙→ Z) ↓ ⊙ua e ]
  domain!-over-⊙equiv {Y = Y} e =
    (! (ap (λ w → f ⊙∘ w) (⊙<–-inv-l e)) ∙ ! (⊙∘-assoc f _ (⊙–> e)))
    ◃ domain-over-⊙equiv (f ⊙∘ (⊙<– e)) e

{- transporting a ptd function along a equivalence or path in the codomain -}
module _ {i} {j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) where

  codomain-over-⊙path : {Z : Ptd j} (p : de⊙ Y == de⊙ Z)
    (q : coe p (pt Y) == pt Z)
    → f == (coe p , q) ⊙∘ f [ (λ W → X ⊙→ W) ↓ ptd= p (↓-idf-in p q) ]
  codomain-over-⊙path idp idp = pair= idp (! (∙-unit-r _ ∙ ap-idf (snd f)))

  codomain-over-⊙equiv : {Z : Ptd j} (e : Y ⊙≃ Z)
    → f == (⊙–> e) ⊙∘ f [ (λ W → X ⊙→ W) ↓ ⊙ua e ]
  codomain-over-⊙equiv {Z = Z} e =
    codomain-over-⊙path (ua (⊙≃-to-≃ e))
      (coe-β (⊙≃-to-≃ e) (pt Y) ∙ snd (⊙–> e))
    ▹ ap (λ w → w ⊙∘ f) (⊙λ= (coe-β (⊙≃-to-≃ e)) (↓-idf=cst-in idp))

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (g : X ⊙→ Z) where

  codomain!-over-⊙path : {Y : Ptd j} (p : de⊙ Y == de⊙ Z)
    (q : coe p (pt Y) == pt Z)
    → (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (pt Y)) ⊙∘ g == g
      [ (λ W → X ⊙→ W) ↓ ptd= p (↓-idf-in p q) ]
  codomain!-over-⊙path idp idp = pair= idp (∙-unit-r _ ∙ ap-idf (snd g))

  codomain!-over-⊙equiv : {Y : Ptd j} (e : Y ⊙≃ Z)
    → (⊙<– e) ⊙∘ g == g [ (λ W → X ⊙→ W) ↓ ⊙ua e ]
  codomain!-over-⊙equiv {Y = Y} e =
    codomain-over-⊙equiv (⊙<– e ⊙∘ g) e
    ▹ ! (⊙∘-assoc (⊙–> e) _ g) ∙ ap (λ w → w ⊙∘ g) (⊙<–-inv-r e) ∙ ⊙∘-unit-l g

{- transporting a group homomorphism along an isomorphism -}

domain-over-iso : ∀ {i j} {G H : Group i} {K : Group j}
  {φ : G →ᴳ H} {ie : is-equiv (GroupHom.f φ)} {ψ : G →ᴳ K} {χ : H →ᴳ K}
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → A → Group.El K) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → J →ᴳ K) ↓ uaᴳ (φ , ie) ]
domain-over-iso {K = K} {φ = φ} {ie} {ψ} {χ} p =
  group-hom=-↓ $ ↓-ap-out _ Group.El _ $
    transport
      (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → A → Group.El K) ↓ q ])
      (! (El=-β (φ , ie)))
      p

codomain-over-iso : ∀ {i j} {G : Group i} {H K : Group j}
  {φ : H →ᴳ K} {ie : is-equiv (GroupHom.f φ)} {ψ : G →ᴳ H} {χ : G →ᴳ K}
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → Group.El G → A) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → G →ᴳ J) ↓ uaᴳ (φ , ie) ]
codomain-over-iso {G = G} {φ = φ} {ie} {ψ} {χ} p =
  group-hom=-↓ $ ↓-ap-out _ Group.El _ $
    transport
      (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → Group.El G → A) ↓ q ])
      (! (El=-β (φ , ie)))
      p
