{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.SuspAdjointLoop where

module SuspAdjointLoop {i j} (X : Ptd i) (Y : Ptd j) where

  private
    A = fst X; a₀ = snd X
    B = fst Y; b₀ = snd Y

  R : {b : B}
    → Σ (Suspension A → B) (λ h → h (north A) == b)
    → Σ (A → (b == b)) (λ k → k a₀ == idp)
  R (h , idp) = 
    (λ a → ap h (merid A a ∙ ! (merid A a₀))) ,
    ap (ap h) (!-inv-r (merid A a₀))

  L : {b : B}
    → Σ (A → (b == b)) (λ k → k a₀ == idp)
    → Σ (Suspension A → B) (λ h → h (north A) == b)
  L {b} (k , _) = (SuspensionRec.f A b b k) , idp

  {- Show that R ∘ L ∼ idf -}

  R-L : {b : B} → ∀ K → R {b} (L K) == K
  R-L {b} (k , kpt) = pair= (λ= R-L-fst) (↓-app=cst-in R-L-snd)
    where
    R-L-fst : (a : A)
      → ap (SuspensionRec.f A b b k) (merid A a ∙ ! (merid A a₀)) == k a
    R-L-fst a = 
      ap-∙ (SuspensionRec.f A b b k) (merid A a) (! (merid A a₀))
      ∙ ap2 _∙_ (SuspensionRec.glue-β A b b k a) 
                (ap-! (SuspensionRec.f A b b k) (merid A a₀) 
                 ∙ ap ! (SuspensionRec.glue-β A b b k a₀ ∙ kpt))
      ∙ ∙-unit-r (k a)

    -- lemmas generalize to do some path induction for R-L-snd
    lemma₁ : ∀ {i} {A : Type i} {x : A} {q : x == x} (α : idp == q)
      (γ : q ∙ ! q == idp) (σ : !-inv-r q == γ ∙ idp)
      → idp == (ap2 _∙_ α (ap ! (α ∙ idp)) ∙ γ) ∙ idp
    lemma₁ idp γ σ = σ

    lemma₂ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a₁ a₂ : A} 
      (p : a₁ == a₂) {q r : f a₁ == f a₂} {s : f a₁ == f a₁}
      (α : ap f p == q) (β : q == r) (γ : q ∙ ! r == s) (δ : s == idp)
      (σ : !-inv-r r == transport (λ t → t ∙ ! r == idp) β (γ ∙ δ))
      → ap (ap f) (!-inv-r p) 
        == (ap-∙ f p (! p) ∙ ap2 _∙_ α (ap-! f p ∙ ap ! (α ∙ β)) ∙ γ) ∙ δ
    lemma₂ f idp {q = q} α idp γ δ σ = J'
      (λ s δ → (γ : q ∙ ! q == s) (σ : !-inv-r q == γ ∙ δ)
        → idp == (ap2 _∙_ α (ap ! (α ∙ idp)) ∙ γ) ∙ δ)
      (lemma₁ α) δ γ σ

    lemma₃ : ∀ {i} {A : Type i} {x : A} {p : x == x} (α : p == idp)
      → idp == transport (λ t → t ∙ idp == idp) α (∙-unit-r p ∙ α)
    lemma₃ = J' 
      (λ p α → idp == transport (λ t → t ∙ idp == idp) α (∙-unit-r p ∙ α))
      idp

    R-L-snd : ap (ap (SuspensionRec.f A b b k)) (!-inv-r (merid A a₀))
           == app= (λ= R-L-fst) a₀ ∙ kpt
    R-L-snd = 
      ap (ap (SuspensionRec.f A b b k)) (!-inv-r (merid A a₀))
        =⟨ lemma₂ (SuspensionRec.f A b b k) (merid A a₀) 
             (SuspensionRec.glue-β A b b k a₀) 
             kpt (∙-unit-r (k a₀)) kpt (lemma₃ kpt) ⟩ 
      R-L-fst a₀ ∙ kpt
        =⟨ ! (app=-β R-L-fst a₀) |in-ctx (λ w → w ∙ kpt) ⟩
      app= (λ= R-L-fst) a₀ ∙ kpt ∎

  {- Show that L ∘ R ∼ idf -}

  L-R : {b : B} → ∀ H → L {b} (R H) == H
  L-R (h , idp) = pair= (λ= L-R-fst) (↓-app=cst-in L-R-snd)
    where
    fst-lemma : ∀ {i j} {A : Type i} {B : Type j} {x y z : A} 
      (f : A → B) (p : x == y) (q : z == y)
      → ap f p == ap f (p ∙ ! q) ∙' ap f q
    fst-lemma _ idp idp = idp

    L-R-fst : (σ : Suspension A) → 
      SuspensionRec.f A (h (north _)) (h (north _)) (fst (R (h , idp))) σ == h σ
    L-R-fst = Suspension-elim A
      idp
      (ap h (merid A a₀))
      (λ a → ↓-='-in $
        ap h (merid A a)
          =⟨ fst-lemma h (merid A a) (merid A a₀) ⟩
        ap h (merid A a ∙ ! (merid A a₀)) ∙' ap h (merid A a₀)
          =⟨ ! (SuspensionRec.glue-β A _ _ _ a) 
             |in-ctx (λ w → w ∙' (ap h (merid A a₀))) ⟩
        ap (fst (L (R (h , idp)))) (merid A a) ∙' ap h (merid A a₀)
        ∎)

    L-R-snd : idp == app= (λ= L-R-fst) (north A) ∙ idp
    L-R-snd = ap (λ w → w ∙ idp) (! (app=-β L-R-fst (north A)))

  {- Show that R respects basepoint -}

  pres-ident : {b : B}
    → R {b} ((λ _ → b) , idp) == ((λ _ → idp) , idp)
  pres-ident {b} = pair= 
    (λ= (λ a → ap-cst b (merid A a ∙ ! (merid A a₀)))) 
    (↓-app=cst-in $ 
      ap (ap (λ _ → b)) (!-inv-r (merid A a₀))
        =⟨ lemma (merid A a₀) b ⟩
      ap-cst b (merid A a₀ ∙ ! (merid A a₀))
        =⟨ ! (app=-β (λ a → ap-cst b (merid A a ∙ ! (merid A a₀))) a₀) ⟩
      app= (λ= (λ a → ap-cst b (merid A a ∙ ! (merid A a₀)))) a₀
        =⟨ ! (∙-unit-r _) ⟩
      app= (λ= (λ a → ap-cst b (merid A a ∙ ! (merid A a₀)))) a₀ ∙ idp
      ∎)
    where
    lemma : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (p : x == y) (b : B)
      → ap (ap (λ _ → b)) (!-inv-r p) == ap-cst b (p ∙ ! p)
    lemma idp b = idp

  {- Show that if there is a composition operation ⊙ on B, then R respects 
     that composition, that is R {b ⊙ c} (F ⊙ G) == R {b} F ∙ R {c} G -}

  -- lift a composition operation on the codomain to the function space
  comp-lift : ∀ {i j} {A : Type i} {B C D : Type j} 
    (a : A) (b : B) (c : C) (_⊙_ : B → C → D)
    → Σ (A → B) (λ f → f a == b)
    → Σ (A → C) (λ g → g a == c)
    → Σ (A → D) (λ h → h a == b ⊙ c)
  comp-lift a b c _⊙_ (f , fpt) (g , gpt) = 
    (λ x → f x ⊙ g x) , ap2 _⊙_ fpt gpt 

  pres-comp-fst : ∀ {i j} {A : Type i} {B : Type j} (f g : A → B) 
    (_⊙_ : B → B → B) {a₁ a₂ : A} (p : a₁ == a₂)
    → ap (λ x → f x ⊙ g x) p == ap2 _⊙_ (ap f p) (ap g p)
  pres-comp-fst f g _⊙_ idp = idp

  pres-comp-snd : ∀ {i j} {A : Type i} {B : Type j} (f g : A → B) 
    (_⊙_ : B → B → B) {a₁ a₂ : A} (q : a₁ == a₂)
    → ap (ap (λ x → f x ⊙ g x)) (!-inv-r q) 
      == pres-comp-fst f g _⊙_ (q ∙ ! q) 
         ∙ ap2 (ap2 _⊙_) (ap (ap f) (!-inv-r q)) (ap (ap g) (!-inv-r q))
  pres-comp-snd f g _⊙_ idp = idp

  pres-comp : {b c : B} (_⊙_ : B → B → B)
    (F : Σ (Suspension A → B) (λ f → f (north A) == b))
    (G : Σ (Suspension A → B) (λ f → f (north A) == c))
    → R (comp-lift (north A) b c _⊙_ F G)
      == comp-lift a₀ idp idp (ap2 _⊙_) (R F) (R G)
  pres-comp _⊙_ (f , idp) (g , idp) = pair= 
    (λ= (λ a → pres-comp-fst f g _⊙_ (merid A a ∙ ! (merid A a₀)))) 
    (↓-app=cst-in $ 
      ap (ap (λ x → f x ⊙ g x)) (!-inv-r (merid A a₀))
        =⟨ pres-comp-snd f g _⊙_ (merid A a₀) ⟩
      pres-comp-fst f g _⊙_ (merid A a₀ ∙ ! (merid A a₀))
        ∙ ap2 (ap2 _⊙_) (ap (ap f) (!-inv-r (merid A a₀))) 
                        (ap (ap g) (!-inv-r (merid A a₀)))
        =⟨ ! (app=-β (λ a → pres-comp-fst f g _⊙_ (merid A a ∙ ! (merid A a₀)))
                     a₀) 
           |in-ctx (λ w → w ∙ ap2 (ap2 _⊙_) 
                                  (ap (ap f) (!-inv-r (merid A a₀))) 
                                  (ap (ap g) (!-inv-r (merid A a₀)))) ⟩
      app= (λ= (λ a → pres-comp-fst f g _⊙_ (merid A a ∙ ! (merid A a₀)))) a₀
      ∙ ap2 (ap2 _⊙_) (ap (ap f) (!-inv-r (merid A a₀))) 
                      (ap (ap g) (!-inv-r (merid A a₀)))
      ∎)

  eqv : fst (Ptd-Susp X ∙→ Y) ≃ fst (X ∙→ Ptd-Ω Y)
  eqv = equiv R L R-L L-R

  ptd-path : (Ptd-Susp X ∙→ Y) == (X ∙→ Ptd-Ω Y)
  ptd-path = ptd-ua eqv pres-ident

  