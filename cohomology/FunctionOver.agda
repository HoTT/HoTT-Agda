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

{- transporting a ptd function along a equivalence or path in the domain -}
module _ {i} {j} {Y : Ptd i} {Z : Ptd j} (g : fst (Y ∙→ Z)) where

  domain-over-ptd-path : {X : Ptd i} (p : fst X == fst Y)
    (q : coe p (snd X) == snd Y)
    → g ∘ptd (coe p , q) == g [ (λ W → fst (W ∙→ Z)) ↓ pair= p (↓-idf-in p q) ]
  domain-over-ptd-path idp idp = idp

  domain-over-ptd-equiv : {X : Ptd i} (e : fst X ≃ fst Y)
    (q : –> e (snd X) == snd Y)
    → g ∘ptd (–> e , q) == g [ (λ W → fst (W ∙→ Z)) ↓ ptd-ua e q ]
  domain-over-ptd-equiv {X = X} e q =
    ap (λ w → g ∘ptd w) lemma
    ◃ domain-over-ptd-path (ua e) (coe-β e (snd X) ∙ q)
    where
    lemma : Path {A = fst (X ∙→ Y)}
      (–> e , q) (coe (ua e) , coe-β e (snd X) ∙ q)
    lemma = pair=
      (λ= (! ∘ coe-β e)) 
      (↓-app=cst-in $ 
        q
          =⟨ ap (λ w → w ∙ q) (! (!-inv-l (coe-β e (snd X))))
             ∙ ∙-assoc (! (coe-β e (snd X))) (coe-β e (snd X)) q ⟩
        ! (coe-β e (snd X)) ∙ coe-β e (snd X) ∙ q
          =⟨ ! (app=-β (! ∘ coe-β e) (snd X))
             |in-ctx (λ w → w ∙ coe-β e (snd X) ∙ q) ⟩
        app= (λ= (! ∘ coe-β e)) (snd X) ∙ coe-β e (snd X) ∙ q ∎)

{- transporting a function along an equivalcence or path in the codomain -}
module _ {i} {j} {A : Type i} {B : Type j} (g : A → B) where

  codomain-over-path : {C : Type j} (p : B == C)
    → g == coe p ∘ g [ (λ D → (A → D)) ↓ p ]
  codomain-over-path idp = idp

  codomain-over-equiv : {C : Type j} (e : B ≃ C)
    → g == –> e ∘ g [ (λ D → (A → D)) ↓ ua e ]
  codomain-over-equiv e = ↓-cst→app-in $ λ _ → ↓-idf-ua-in e idp

{- transporting a ptd function along a equivalence or path in the codomain -}
module _ {i} {j} {X : Ptd i} {Y : Ptd j} (g : fst (X ∙→ Y)) where

  codomain-over-ptd-path : {Z : Ptd j} (p : fst Y == fst Z)
    (q : coe p (snd Y) == snd Z)
    → g == (coe p , q) ∘ptd g [ (λ W → fst (X ∙→ W)) ↓ pair= p (↓-idf-in p q) ]
  codomain-over-ptd-path idp idp = pair= idp (! (∙-unit-r _ ∙ ap-idf (snd g)))

  codomain-over-ptd-equiv : {Z : Ptd j} (e : fst Y ≃ fst Z)
    (q : –> e (snd Y) == snd Z)
    → g == (–> e , q) ∘ptd g [ (λ W → fst (X ∙→ W)) ↓ ptd-ua e q ]
  codomain-over-ptd-equiv {Z = Z} e q = 
    codomain-over-ptd-path (ua e) (coe-β e (snd Y) ∙ q)
    ▹ ap (λ w → w ∘ptd g) lemma
    where
    lemma : Path {A = fst (Y ∙→ Z)}
      (coe (ua e) , coe-β e (snd Y) ∙ q) (–> e , q)
    lemma = pair=
      (λ= (coe-β e))
      (↓-app=cst-in $
        coe-β e (snd Y) ∙ q
          =⟨ ! (app=-β (coe-β e) (snd Y)) |in-ctx (λ w → w ∙ q) ⟩
        app= (λ= (coe-β e)) (snd Y) ∙ q ∎)
