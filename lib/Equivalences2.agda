{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths

module lib.Equivalences2 where

{- Pre- and post- composition with equivalences are equivalences -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         {h : A → B} (e : is-equiv h) where

  pre∘-is-equiv : is-equiv (λ (k : C → A) → h ∘ k)
  pre∘-is-equiv = is-eq f g f-g g-f
    where f = λ k → h ∘ k
          g = λ k → is-equiv.g e ∘ k
          f-g = λ k → ap (λ q → q ∘ k) (λ= $ is-equiv.f-g e)
          g-f = λ k → ap (λ q → q ∘ k) (λ= $ is-equiv.g-f e)

  post∘-is-equiv : is-equiv (λ (k : B → C) → k ∘ h)
  post∘-is-equiv = is-eq f g f-g g-f
    where f = λ k → k ∘ h
          g = λ k → k ∘ is-equiv.g e
          f-g = λ k → ap (λ q → λ x → k (q x)) (λ= $ is-equiv.g-f e)
          g-f = λ k → ap (λ q → λ x → k (q x)) (λ= $ is-equiv.f-g e)

is-contr-map : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  → Type (lmax i j)
is-contr-map {A = A} {B = B} f = (y : B) → is-contr (Σ A (λ x → f x == y))

equiv-is-contr-map : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-equiv f → is-contr-map f)
equiv-is-contr-map e y =
   equiv-preserves-level ((equiv-Σ-fst (λ z → z == y) e) ⁻¹) (pathto-is-contr y)

contr-map-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-contr-map f → is-equiv f)
contr-map-is-equiv {f = f} cm = is-eq _
  (λ b → fst (fst (cm b)))
  (λ b → snd (fst (cm b)))
  (λ a → ap fst (snd (cm (f a)) (a , idp)))


fiber=-eqv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B} {y : B}
  (r s : Σ A (λ x → h x == y))
  → (r == s) ≃ Σ (fst r == fst s) (λ γ → ap h γ ∙ snd s == snd r)
fiber=-eqv r s = equiv-Σ-snd (λ γ → !-equiv ∘e (↓-app=cst-eqv ⁻¹)) ∘e ((=Σ-eqv r s)⁻¹)


module _ {i j} {A : Type i} {B : Type j} where

  linv : (A → B) → Type (lmax i j)
  linv f = Σ (B → A) (λ g → (∀ x → g (f x) == x))

  rinv : (A → B) → Type (lmax i j)
  rinv f = Σ (B → A) (λ g → (∀ y → f (g y) == y))

  lcoh : (f : A → B) → linv f → Type (lmax i j)
  lcoh f (g , g-f) = Σ (∀ y → f (g y) == y)
                       (λ f-g → ∀ y → ap g (f-g y) == g-f (g y))

  rcoh : (f : A → B) → rinv f → Type (lmax i j)
  rcoh f (g , f-g) = Σ (∀ x → g (f x) == x)
                       (λ g-f → ∀ x → ap f (g-f x) == f-g (f x))


module _ {i j} {A : Type i} {B : Type j} {f : A → B} (e : is-equiv f) where

  equiv-linv-is-contr : is-contr (linv f)
  equiv-linv-is-contr = equiv-preserves-level (equiv-Σ-snd (λ _ → λ=-equiv ⁻¹))
                          (equiv-is-contr-map (post∘-is-equiv e) (idf A))

  equiv-rinv-is-contr : is-contr (rinv f)
  equiv-rinv-is-contr = equiv-preserves-level (equiv-Σ-snd (λ _ → λ=-equiv ⁻¹))
                          (equiv-is-contr-map (pre∘-is-equiv e) (idf B))

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  rcoh-eqv : (v : rinv f)
    → rcoh f v ≃ Π A (λ x → (fst v (f x) , snd v (f x)) == (x , idp {a = f x}))
  rcoh-eqv v = equiv-Π-r (λ x → ((fiber=-eqv {h = f} _ _)⁻¹) ∘e apply-unit-r x) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ x → Σ _ (λ γ → ap f γ == _) ≃ Σ _ (λ γ → ap f γ ∙ idp == _)
      apply-unit-r x = equiv-Σ-snd $
        λ γ → coe-equiv (ap (λ q → q == snd v (f x)) (! (∙-unit-r _)))

  lcoh-eqv : (v : linv f)
    → lcoh f v ≃ Π B (λ y → (f (fst v y) , snd v (fst v y)) == (y , idp))
  lcoh-eqv v = equiv-Π-r (λ y → ((fiber=-eqv {h = fst v} _ _)⁻¹) ∘e apply-unit-r y) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ y → Σ _ (λ γ → ap (fst v) γ == _) ≃ Σ _ (λ γ → ap (fst v) γ ∙ idp == _)
      apply-unit-r y = equiv-Σ-snd $
        λ γ → coe-equiv (ap (λ q → q == snd v (fst v y)) (! (∙-unit-r _)))


equiv-rcoh-is-contr : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                      (e : is-equiv f) → (v : rinv f) → is-contr (rcoh f v)
equiv-rcoh-is-contr {f = f} e v = equiv-preserves-level ((rcoh-eqv v)⁻¹)
  (Π-level (λ x → =-preserves-level ⟨-2⟩ (equiv-is-contr-map e (f x))))

rinv-and-rcoh-eqv-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B}
  → Σ (rinv h) (rcoh h) ≃ is-equiv h
rinv-and-rcoh-eqv-is-equiv {h = h} = equiv f g (λ _ → idp) (λ _ → idp)
  where f : Σ (rinv h) (rcoh h) → is-equiv h
        f s = record {g = fst (fst s); f-g = snd (fst s);
                      g-f = fst (snd s); adj = snd (snd s)}
        g : is-equiv h → Σ (rinv h) (rcoh h)
        g t = ((is-equiv.g t , is-equiv.f-g t) , (is-equiv.g-f t , is-equiv.adj t))

is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  → is-prop (is-equiv f)
is-equiv-is-prop _ = inhab-to-contr-is-prop $ λ e →
  equiv-preserves-level rinv-and-rcoh-eqv-is-equiv
    (Σ-level (equiv-rinv-is-contr e) (equiv-rcoh-is-contr e))

∘e-unit-r : ∀ {i} {A B : Type i} (e : A ≃ B) → (e ∘e ide A) == e
∘e-unit-r e =
  pair= idp (prop-has-all-paths (is-equiv-is-prop (fst e)) _ _)

ua-∘e : ∀ {i} {A B : Type i}
  (e₁ : A ≃ B) {C : Type i} (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂
ua-∘e =
  equiv-induction
    (λ {A} {B} e₁ → ∀ {C} → ∀ (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂)
    (λ A → λ e₂ → ap ua (∘e-unit-r e₂) ∙ ap (λ w → (w ∙ ua e₂)) (! (ua-η idp)))
