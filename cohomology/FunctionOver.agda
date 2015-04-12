{-# OPTIONS --without-K #-}

open import HoTT

{- Useful lemmas for computing the effect of transporting a function
 - across an equivalence in the domain or codomain.
 - TODO: find a better place for this. -}

module cohomology.FunctionOver where

{- transporting a function along an equivalence or path in the domain -}
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

  domain-over-⊙equiv : {X : Ptd i} (e : X ⊙≃ Y)
    → g ⊙∘ ⊙–> e == g [ (λ W → fst (W ⊙→ Z)) ↓ ⊙ua e ]
  domain-over-⊙equiv {X = X} e =
    ap (λ w → g ⊙∘ w) (! $ ⊙λ= (coe-β (⊙≃-to-≃ e)) idp)
    ◃ domain-over-⊙path (ua (⊙≃-to-≃ e))
                        (coe-β (⊙≃-to-≃ e) (snd X) ∙ snd (⊙–> e))

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (f : fst (X ⊙→ Z)) where

  domain!-over-⊙path : {Y : Ptd i} (p : fst X == fst Y)
    (q : coe p (snd X) == snd Y)
    → f == f ⊙∘ (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (snd X))
      [ (λ W → fst (W ⊙→ Z)) ↓ pair= p (↓-idf-in p q) ]
  domain!-over-⊙path idp idp = idp

  domain!-over-⊙equiv : {Y : Ptd i} (e : X ⊙≃ Y)
    → f == f ⊙∘ (⊙<– e) [ (λ W → fst (W ⊙→ Z)) ↓ ⊙ua e ]
  domain!-over-⊙equiv {Y = Y} e =
    (! (ap (λ w → f ⊙∘ w) (⊙<–-inv-l e)) ∙ ! (⊙∘-assoc f _ (⊙–> e)))
    ◃ domain-over-⊙equiv (f ⊙∘ (⊙<– e)) e

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

  codomain-over-⊙equiv : {Z : Ptd j} (e : Y ⊙≃ Z)
    → f == (⊙–> e) ⊙∘ f [ (λ W → fst (X ⊙→ W)) ↓ ⊙ua e ]
  codomain-over-⊙equiv {Z = Z} e =
    codomain-over-⊙path (ua (⊙≃-to-≃ e))
      (coe-β (⊙≃-to-≃ e) (snd Y) ∙ snd (⊙–> e))
    ▹ ap (λ w → w ⊙∘ f) (⊙λ= (coe-β (⊙≃-to-≃ e)) idp)

module _ {i} {j} {X : Ptd i} {Z : Ptd j} (g : fst (X ⊙→ Z)) where

  codomain!-over-⊙path : {Y : Ptd j} (p : fst Y == fst Z)
    (q : coe p (snd Y) == snd Z)
    → (coe! p , ap (coe! p) (! q) ∙ coe!-inv-l p (snd Y)) ⊙∘ g == g
      [ (λ W → fst (X ⊙→ W)) ↓ pair= p (↓-idf-in p q) ]
  codomain!-over-⊙path idp idp = pair= idp (∙-unit-r _ ∙ ap-idf (snd g))

  codomain!-over-⊙equiv : {Y : Ptd j} (e : Y ⊙≃ Z)
    → (⊙<– e) ⊙∘ g == g [ (λ W → fst (X ⊙→ W)) ↓ ⊙ua e ]
  codomain!-over-⊙equiv {Y = Y} e =
    codomain-over-⊙equiv (⊙<– e ⊙∘ g) e
    ▹ ! (⊙∘-assoc (⊙–> e) _ g) ∙ ap (λ w → w ⊙∘ g) (⊙<–-inv-r e) ∙ ⊙∘-unit-l g

module _ {i j} where

  function-over-paths : {A₁ B₁ : Type i} {A₂ B₂ : Type j}
    {f : A₁ → A₂} {g : B₁ → B₂} (p₁ : A₁ == B₁) (p₂ : A₂ == B₂)
    → coe p₂ ∘ f == g ∘ coe p₁
    → f == g [ (λ {(A , B) → A → B}) ↓ pair×= p₁ p₂ ]
  function-over-paths idp idp α = α

  function-over-equivs : {A₁ B₁ : Type i} {A₂ B₂ : Type j}
    {f : A₁ → A₂} {g : B₁ → B₂} (e₁ : A₁ ≃ B₁) (e₂ : A₂ ≃ B₂)
    → –> e₂ ∘ f == g ∘ –> e₁
    → f == g [ (λ {(A , B) → A → B}) ↓ pair×= (ua e₁) (ua e₂) ]
  function-over-equivs {f = f} {g = g} e₁ e₂ α =
    function-over-paths (ua e₁) (ua e₂) $
      transport (λ {(h , k) → h ∘ f == g ∘ k})
        (pair×= (! (λ= (coe-β e₂))) (! (λ= (coe-β e₁)))) α

{- transporting a group homomorphism along an isomorphism -}

domain-over-iso : ∀ {i j} {G H : Group i} {K : Group j}
  {φ : G →ᴳ H} {ie : is-equiv (GroupHom.f φ)} {ψ : G →ᴳ K} {χ : H →ᴳ K}
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → A → Group.El K) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → J →ᴳ K) ↓ group-ua (φ , ie) ]
domain-over-iso {K = K} {φ = φ} {ie} {ψ} {χ} p =
  hom=-↓ _ _ $ ↓-ap-out _ Group.El _ $
    transport
      (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → A → Group.El K) ↓ q ])
      (! (group-ua-el (φ , ie)))
      p

codomain-over-iso : ∀ {i j} {G : Group i} {H K : Group j}
  {φ : H →ᴳ K} {ie : is-equiv (GroupHom.f φ)} {ψ : G →ᴳ H} {χ : G →ᴳ K}
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ A → Group.El G → A) ↓ ua (GroupHom.f φ , ie) ]
  → ψ == χ [ (λ J → G →ᴳ J) ↓ group-ua (φ , ie) ]
codomain-over-iso {G = G} {φ = φ} {ie} {ψ} {χ} p =
  hom=-↓ _ _ $ ↓-ap-out _ Group.El _ $
    transport
      (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ A → Group.El G → A) ↓ q ])
      (! (group-ua-el (φ , ie)))
      p

hom-over-isos : ∀ {i j} {G₁ H₁ : Group i} {G₂ H₂ : Group j}
  {φ₁ : G₁ →ᴳ H₁} {ie₁ : is-equiv (GroupHom.f φ₁)}
  {φ₂ : G₂ →ᴳ H₂} {ie₂ : is-equiv (GroupHom.f φ₂)}
  {ψ : G₁ →ᴳ G₂} {χ : H₁ →ᴳ H₂}
  → GroupHom.f ψ == GroupHom.f χ
    [ (λ {(A , B) → A → B}) ↓ pair×= (ua (GroupHom.f φ₁ , ie₁))
                                     (ua (GroupHom.f φ₂ , ie₂)) ]
  → ψ == χ [ uncurry _→ᴳ_ ↓ pair×= (group-ua (φ₁ , ie₁)) (group-ua (φ₂ , ie₂)) ]
hom-over-isos {φ₁ = φ₁} {ie₁} {φ₂} {ie₂} {ψ} {χ} p = hom=-↓ _ _ $
  ↓-ap-out (λ {(A , B) → A → B}) (λ {(G , H) → (Group.El G , Group.El H)}) _ $
    transport
      (λ q → GroupHom.f ψ == GroupHom.f χ [ (λ {(A , B) → A → B}) ↓ q ])
      (ap2 (λ p q → pair×= p q) (! (group-ua-el (φ₁ , ie₁)))
                                (! (group-ua-el (φ₂ , ie₂)))
       ∙ ! (lemma Group.El Group.El
             (group-ua (φ₁ , ie₁)) (group-ua (φ₂ , ie₂))))
      p
  where
  lemma : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
    (f : A → C) (g : B → D) {x y : A} {w z : B} (p : x == y) (q : w == z)
    → ap (λ {(a , b) → (f a , g b)}) (pair×= p q)
      == pair×= (ap f p) (ap g q)
  lemma f g idp idp = idp
