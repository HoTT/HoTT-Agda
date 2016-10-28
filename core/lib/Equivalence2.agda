{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.Unit
open import lib.types.Empty

module lib.Equivalence2 where

{- Pre- and post- composition with equivalences are equivalences -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         {h : A → B} (e : is-equiv h) where

  pre∘-is-equiv : is-equiv (λ (k : B → C) → k ∘ h)
  pre∘-is-equiv = is-eq f g f-g g-f
    where f = _∘ h
          g = _∘ is-equiv.g e
          f-g = λ k → ap (k ∘_) (λ= $ is-equiv.g-f e)
          g-f = λ k → ap (k ∘_) (λ= $ is-equiv.f-g e)

  post∘-is-equiv : is-equiv (λ (k : C → A) → h ∘ k)
  post∘-is-equiv = is-eq f g f-g g-f
    where f = h ∘_
          g = is-equiv.g e ∘_
          f-g = λ k → ap (_∘ k) (λ= $ is-equiv.f-g e)
          g-f = λ k → ap (_∘ k) (λ= $ is-equiv.g-f e)

{- The same thing on the abstraction level of equivalences -}
module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
         (e : A ≃ B) where

  pre∘-equiv : (B → C) ≃ (A → C)
  pre∘-equiv = (_ , pre∘-is-equiv (snd e))

  post∘-equiv : (C → A) ≃ (C → B)
  post∘-equiv = (_ , post∘-is-equiv (snd e))

is-contr-map : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  → Type (lmax i j)
is-contr-map {A = A} {B = B} f = (y : B) → is-contr (hfiber f y)

equiv-is-contr-map : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-equiv f → is-contr-map f)
equiv-is-contr-map e y =
   equiv-preserves-level (Σ-emap-l (_== y) (_ , e) ⁻¹) (pathto-is-contr y)

contr-map-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → (is-contr-map f → is-equiv f)
contr-map-is-equiv {f = f} cm = is-eq _
  (λ b → fst (fst (cm b)))
  (λ b → snd (fst (cm b)))
  (λ a → ap fst (snd (cm (f a)) (a , idp)))


fiber=-econv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B} {y : B}
  (r s : Σ A (λ x → h x == y))
  → (r == s) ≃ Σ (fst r == fst s) (λ γ → ap h γ ∙ snd s == snd r)
fiber=-econv r s = Σ-emap-r (λ γ → !-equiv ∘e (↓-app=cst-econv ⁻¹)) ∘e ((=Σ-econv r s)⁻¹)


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
  equiv-linv-is-contr = equiv-preserves-level (Σ-emap-r λ _ → λ=-equiv ⁻¹)
                          (equiv-is-contr-map (pre∘-is-equiv e) (idf A))

  equiv-rinv-is-contr : is-contr (rinv f)
  equiv-rinv-is-contr = equiv-preserves-level (Σ-emap-r λ _ → λ=-equiv ⁻¹)
                          (equiv-is-contr-map (post∘-is-equiv e) (idf B))

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  rcoh-econv : (v : rinv f)
    → rcoh f v ≃ Π A (λ x → (fst v (f x) , snd v (f x)) == (x , idp {a = f x}))
  rcoh-econv v = Π-emap-r (λ x → ((fiber=-econv {h = f} _ _)⁻¹) ∘e apply-unit-r x) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ x → Σ _ (λ γ → ap f γ == _) ≃ Σ _ (λ γ → ap f γ ∙ idp == _)
      apply-unit-r x = Σ-emap-r λ γ
        → coe-equiv (ap (λ q → q == snd v (f x)) (! (∙-unit-r _)))

  lcoh-econv : (v : linv f)
    → lcoh f v ≃ Π B (λ y → (f (fst v y) , snd v (fst v y)) == (y , idp))
  lcoh-econv v = Π-emap-r (λ y → ((fiber=-econv {h = fst v} _ _)⁻¹) ∘e apply-unit-r y) ∘e choice ⁻¹
    where
      apply-unit-r : ∀ y → Σ _ (λ γ → ap (fst v) γ == _) ≃ Σ _ (λ γ → ap (fst v) γ ∙ idp == _)
      apply-unit-r y = Σ-emap-r λ γ
        → coe-equiv (ap (λ q → q == snd v (fst v y)) (! (∙-unit-r _)))


equiv-rcoh-is-contr : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
                      (e : is-equiv f) → (v : rinv f) → is-contr (rcoh f v)
equiv-rcoh-is-contr {f = f} e v = equiv-preserves-level ((rcoh-econv v)⁻¹)
  (Π-level (λ x → =-preserves-level -2 (equiv-is-contr-map e (f x))))

rinv-and-rcoh-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {h : A → B}
  → Σ (rinv h) (rcoh h) ≃ is-equiv h
rinv-and-rcoh-is-equiv {h = h} = equiv f g (λ _ → idp) (λ _ → idp)
  where f : Σ (rinv h) (rcoh h) → is-equiv h
        f s = record {g = fst (fst s); f-g = snd (fst s);
                      g-f = fst (snd s); adj = snd (snd s)}
        g : is-equiv h → Σ (rinv h) (rcoh h)
        g t = ((is-equiv.g t , is-equiv.f-g t) , (is-equiv.g-f t , is-equiv.adj t))

is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} {f : A → B}
  → is-prop (is-equiv f)
is-equiv-is-prop = inhab-to-contr-is-prop λ e →
  equiv-preserves-level rinv-and-rcoh-is-equiv
    (Σ-level (equiv-rinv-is-contr e) (equiv-rcoh-is-contr e))

is-equiv-prop : ∀ {i j} {A : Type i} {B : Type j}
  → SubtypeProp (A → B) (lmax i j)
is-equiv-prop = is-equiv , λ f → is-equiv-is-prop

∘e-unit-r : ∀ {i} {A B : Type i} (e : A ≃ B) → (e ∘e ide A) == e
∘e-unit-r e = pair= idp (prop-has-all-paths is-equiv-is-prop _ _)

ua-∘e : ∀ {i} {A B : Type i}
  (e₁ : A ≃ B) {C : Type i} (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂
ua-∘e =
  equiv-induction
    (λ {A} {B} e₁ → ∀ {C} → ∀ (e₂ : B ≃ C) → ua (e₂ ∘e e₁) == ua e₁ ∙ ua e₂)
    (λ A → λ e₂ → ap ua (∘e-unit-r e₂) ∙ ap (λ w → (w ∙ ua e₂)) (! (ua-η idp)))

{- Not sure about the interface.

{- Adjointion where hom = path -}

module _ {i j} {A : Type i} {B : Type j} (e : A ≃ B) where

  =-adjunct : ∀ {a b} → (–> e a == b) → (a == <– e b)
  =-adjunct p = ! (<–-inv-l e _) ∙ ap (<– e) p

  =-adjunct' : ∀ {a b} → (a == <– e b) → (–> e a == b)
  =-adjunct' p = ap (–> e) p ∙ (<–-inv-r e _)
-}

{- Type former equivalences involving Empty may require λ=. -}
module _ {j} {B : Empty → Type j} where
  Σ₁-Empty : Σ Empty B ≃ Empty
  Σ₁-Empty = equiv (⊥-rec ∘ fst) ⊥-rec ⊥-elim (⊥-rec ∘ fst)

  Π₁-Empty : Π Empty B ≃ Unit
  Π₁-Empty = equiv (cst tt) (cst ⊥-elim) (λ _ → contr-has-all-paths Unit-is-contr _ _) (λ _ → λ= ⊥-elim)

Σ₂-Empty : ∀ {i} {A : Type i} → Σ A (λ _ → Empty) ≃ Empty
Σ₂-Empty = equiv (⊥-rec ∘ snd) ⊥-rec ⊥-elim (⊥-rec ∘ snd)

{- Fiberwise equivalence -}
module _ {i j k} {A : Type i} {P : A → Type j} {Q : A → Type k}
  (f : ∀ x → P x → Q x) where

  private
    f-tot : Σ A P → Σ A Q
    f-tot (x , y) = x , f x y

  fiber-equiv-is-total-equiv : (∀ x → is-equiv (f x)) → is-equiv f-tot
  fiber-equiv-is-total-equiv f-ise = is-eq _ from to-from from-to
    where
      from : Σ A Q → Σ A P
      from (x , y) = x , is-equiv.g (f-ise x) y

      abstract
        to-from : ∀ q → f-tot (from q) == q
        to-from (x , q) = pair= idp (is-equiv.f-g (f-ise x) q)

        from-to : ∀ p → from (f-tot p) == p
        from-to (x , p) = pair= idp (is-equiv.g-f (f-ise x) p)

  total-equiv-is-fiber-equiv : is-equiv f-tot → (∀ x → is-equiv (f x))
  total-equiv-is-fiber-equiv f-tot-ise x = is-eq _ from to-from from-to
    where
      module f-tot = is-equiv f-tot-ise

      from : Q x → P x
      from q = transport P (fst= (f-tot.f-g (x , q))) (snd (f-tot.g (x , q)))

      abstract
        from-lemma : ∀ q → snd (f-tot.g (x , q)) == from q
          [ P ↓ fst= (f-tot.f-g (x , q)) ]
        from-lemma q = from-transp P (fst= (f-tot.f-g (x , q))) idp

        to-from : ∀ q → f x (from q) == q
        to-from q =
          transport (λ path → f x (from q) == q [ Q ↓ path ])
            (!-inv-l (fst= (f-tot.f-g (x , q))))
            (!ᵈ (ap↓ (λ {x} → f x) (from-lemma q)) ∙ᵈ snd= (f-tot.f-g (x , q)))

        from-to : ∀ p → from (f x p) == p
        from-to p =
          transport (λ path → from (f x p) == p [ P ↓ path ])
            ( ap (λ path → ! path ∙ fst= (f-tot.g-f (x , p)))
                (ap fst= (! (f-tot.adj (x , p))) ∙ ∘-ap fst f-tot (f-tot.g-f (x , p)))
            ∙ !-inv-l (fst= (f-tot.g-f (x , p))))
            (!ᵈ (from-lemma (f x p)) ∙ᵈ snd= (f-tot.g-f (x , p)))
