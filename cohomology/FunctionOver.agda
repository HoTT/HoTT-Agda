{-# OPTIONS --without-K #-}

open import HoTT

{- Useful lemmas for computing the effect of transporting a function
 - across an equivalence in the domain or codomain -}

module cohomology.FunctionOver where

{- transporting a function along an equivalcence or path in the domain -}
module _ {i} {j} {B : Type i} {C : Type j} (g : B → C) where

  domain-over-path : {A : Type i} (p : A == B)
    → g ∘ coe p == g [ (λ D → (D → C)) ↓ p ]
  domain-over-path idp = idp

  domain-over-equiv : {A : Type i} (e : A ≃ B)
    → g ∘ –> e == g [ (λ D → (D → C)) ↓ ua e ]
  domain-over-equiv e = ↓-app→cst-in $ λ q → ap g (↓-idf-ua-out e q)

module _ {i} {j} {A : Type i} {C : Type j} (f : A → C) where

  domain!-over-path : {B : Type i} (p : A == B)
    → f == f ∘ coe! p [ (λ D → (D → C)) ↓ p ]
  domain!-over-path idp = idp

  domain!-over-equiv : {B : Type i} (e : A ≃ B)
    → f == f ∘ <– e [ (λ D → (D → C)) ↓ ua e ]
  domain!-over-equiv e = ↓-app→cst-in $
    λ q → ap f (! (<–-inv-l e _) ∙ ap (<– e) (↓-idf-ua-out e q))

{- transporting a ptd function along a equivalence or path in the domain -}
module _ {i} {j} {Y : Ptd i} {Z : Ptd j} (g : fst (Y ⊙→ Z)) where

  domain-over-⊙path : {X : Ptd i} (p : fst X == fst Y)
    (q : coe p (snd X) == snd Y)
    → g ⊙∘ (coe p , q) == g [ (λ W → fst (W ⊙→ Z)) ↓ pair= p (↓-idf-in p q) ]
  domain-over-⊙path idp idp = idp

  domain-over-⊙equiv : {X : Ptd i} (e : fst X ≃ fst Y)
    (q : –> e (snd X) == snd Y)
    → g ⊙∘ ⊙–> e q == g [ (λ W → fst (W ⊙→ Z)) ↓ ⊙ua e q ]
  domain-over-⊙equiv {X = X} e q =
    ap (λ w → g ⊙∘ w) lemma ◃ domain-over-⊙path (ua e) (coe-β e (snd X) ∙ q)
    where
    lemma : Path {A = fst (X ⊙→ Y)}
       (⊙–> e q) (coe (ua e) , coe-β e (snd X) ∙ q)
    lemma = ! $ ⊙λ= (coe-β e) idp

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (f : fst (X ⊙→ Z)) where

  domain!-over-⊙path : {Y : Ptd i} (p : fst X == fst Y)
    (q : coe p (snd X) == snd Y)
    → f == f ⊙∘ (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (snd X))
      [ (λ W → fst (W ⊙→ Z)) ↓ pair= p (↓-idf-in p q) ]
  domain!-over-⊙path idp idp = idp

  domain!-over-⊙equiv : {Y : Ptd i} (e : fst X ≃ fst Y)
    (q : –> e (snd X) == snd Y)
    → f == f ⊙∘ (⊙<– e q) [ (λ W → fst (W ⊙→ Z)) ↓ ⊙ua e q ]
  domain!-over-⊙equiv {Y = Y} e q =
    (ap (λ w → f ⊙∘ w) (lemma e q) ∙ ! (⊙∘-assoc f _ (–> e , q))) ◃
    domain-over-⊙equiv
      (f ⊙∘ (<– e , ap (<– e) (! q) ∙ <–-inv-l e (snd X))) e q
    where
    lemma : {X Y : Ptd i}
      (e : fst X ≃ fst Y) (q : –> e (snd X) == snd Y)
      → ⊙idf X == ((<– e , ap (<– e) (! q) ∙ <–-inv-l e (snd X)) ⊙∘ (–> e , q))
    lemma {X = X} e idp = ! $ ⊙λ= (<–-inv-l e) (! (∙-unit-r _))

{- transporting a function along an equivalence or path in the codomain -}
module _ {i} {j} {A : Type i} {B : Type j} (f : A → B) where

  codomain-over-path : {C : Type j} (p : B == C)
    → f == coe p ∘ f [ (λ D → (A → D)) ↓ p ]
  codomain-over-path idp = idp

  codomain-over-equiv : {C : Type j} (e : B ≃ C)
    → f == –> e ∘ f [ (λ D → (A → D)) ↓ ua e ]
  codomain-over-equiv e = ↓-cst→app-in $ λ _ → ↓-idf-ua-in e idp

module _ {i} {j} {A : Type i} {C : Type j} (g : A → C) where

  codomain!-over-path : {B : Type j} (p : B == C)
    → coe! p ∘ g == g [ (λ D → (A → D)) ↓ p ]
  codomain!-over-path idp = idp

  codomain!-over-equiv : {B : Type j} (e : B ≃ C)
    → <– e ∘ g == g [ (λ D → (A → D)) ↓ ua e ]
  codomain!-over-equiv e = ↓-cst→app-in $ λ _ → ↓-idf-ua-in e (<–-inv-r e _)

{- transporting a ptd function along a equivalence or path in the codomain -}
module _ {i} {j} {X : Ptd i} {Y : Ptd j} (f : fst (X ⊙→ Y)) where

  codomain-over-⊙path : {Z : Ptd j} (p : fst Y == fst Z)
    (q : coe p (snd Y) == snd Z)
    → f == (coe p , q) ⊙∘ f [ (λ W → fst (X ⊙→ W)) ↓ pair= p (↓-idf-in p q) ]
  codomain-over-⊙path idp idp = pair= idp (! (∙-unit-r _ ∙ ap-idf (snd f)))

  codomain-over-⊙equiv : {Z : Ptd j} (e : fst Y ≃ fst Z)
    (q : –> e (snd Y) == snd Z)
    → f == (–> e , q) ⊙∘ f [ (λ W → fst (X ⊙→ W)) ↓ ⊙ua e q ]
  codomain-over-⊙equiv {Z = Z} e q =
    codomain-over-⊙path (ua e) (coe-β e (snd Y) ∙ q) ▹ ap (λ w → w ⊙∘ f) lemma
    where
    lemma : Path {A = fst (Y ⊙→ Z)}
      (coe (ua e) , coe-β e (snd Y) ∙ q) (–> e , q)
    lemma = ⊙λ= (coe-β e) idp

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (g : fst (X ⊙→ Z)) where

  codomain!-over-⊙path : {Y : Ptd j} (p : fst Y == fst Z)
    (q : coe p (snd Y) == snd Z)
    → (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (snd Y)) ⊙∘ g == g
      [ (λ W → fst (X ⊙→ W)) ↓ pair= p (↓-idf-in p q) ]
  codomain!-over-⊙path idp idp = pair= idp (∙-unit-r _ ∙ ap-idf (snd g))

  codomain!-over-⊙equiv : {Y : Ptd j} (e : fst Y ≃ fst Z)
    (q : –> e (snd Y) == snd Z)
    → (⊙<– e q) ⊙∘ g == g [ (λ W → fst (X ⊙→ W)) ↓ ⊙ua e q ]
  codomain!-over-⊙equiv {Y = Y} e q =
    codomain-over-⊙equiv
      ((<– e , ap (<– e) (! q) ∙ <–-inv-l e (snd Y)) ⊙∘ g) e q
    ▹ (! (⊙∘-assoc (–> e , q) _ g) ∙ ap (λ w → w ⊙∘ g) (lemma e q)
       ∙ ⊙∘-unit-l g)
    where
    lemma : {Y Z : Ptd j}
      (e : fst Y ≃ fst Z) (q : –> e (snd Y) == snd Z)
      → ((–> e , q) ⊙∘ (<– e , ap (<– e) (! q) ∙ <–-inv-l e (snd Y))) == ⊙idf Z
    lemma {Y = Y} e idp =
      ⊙λ= (<–-inv-r e) (ap (λ w → w ∙ idp) (<–-inv-adj e (snd Y)))

{- transporting a group homomorphism along an isomorphism -}

domain-over-iso : ∀ {i j} {G H : Group i} {K : Group j}
  (φ : G →ᴳ H) (ie : is-equiv (GroupHom.f φ)) (ψ : G →ᴳ K) (χ : H →ᴳ K)
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → A → Group.El K) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → J →ᴳ K) ↓ group-ua (φ , ie) ]
domain-over-iso {K = K} φ ie ψ χ p = hom=-↓ _ _ $ ↓-ap-out _ Group.El _ $
  transport
    (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → A → Group.El K) ↓ q ])
    (! (group-ua-el (φ , ie)))
    p

codomain-over-iso : ∀ {i j} {G : Group i} {H K : Group j}
  (φ : H →ᴳ K) (ie : is-equiv (GroupHom.f φ)) (ψ : G →ᴳ H) (χ : G →ᴳ K)
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → Group.El G → A) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → G →ᴳ J) ↓ group-ua (φ , ie) ]
codomain-over-iso {G = G} φ ie ψ χ p = hom=-↓ _ _ $ ↓-ap-out _ Group.El _ $
  transport
    (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → Group.El G → A) ↓ q ])
    (! (group-ua-el (φ , ie)))
    p
