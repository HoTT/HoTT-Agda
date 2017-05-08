{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma

module lib.types.Modality where

  -- Where to put this?  Or maybe there's
  -- a simpler proof from some library function?
  !ᵈ-inv-l-out : ∀ {ℓ} {A : Type ℓ} {P : A → Type ℓ}
    {a₀ a₁ : A} {p : a₀ == a₁} {x₀ x₁ : P a₁} 
    → (q : x₀ == x₁ [ P ↓ ! p ∙ p ])
    → x₀ == x₁
  !ᵈ-inv-l-out {p = idp} q = q

  record Modality ℓ : Type (lsucc ℓ) where
    field

      is-local : Type ℓ → Type ℓ
      is-local-is-prop : {A : Type ℓ} → is-prop (is-local A)

      ◯ : Type ℓ → Type ℓ
      ◯-is-local : {A : Type ℓ} → is-local (◯ A)

      η : {A : Type ℓ} → A → ◯ A

      ◯-elim : {A : Type ℓ} {B : ◯ A → Type ℓ}
        (B-local : (x : ◯ A) → is-local (B x))
        → Π A (B ∘ η) → Π (◯ A) B

      ◯-elim-β : {A : Type ℓ} {B : ◯ A → Type ℓ}
        (B-local : (x : ◯ A) → is-local (B x)) (f : Π A (B ∘ η))
        → (a : A) → ◯-elim B-local f (η a) == f a

      ◯-=-is-local : {A : Type ℓ} (a₀ a₁ : ◯ A) → is-local (a₀ == a₁)

    ◯-Type : Type (lsucc ℓ)
    ◯-Type = Σ (Type ℓ) is-local

    {- elimination rules -}

    module ◯Elim {A : Type ℓ} {B : ◯ A → Type ℓ}
      (B-local : (x : ◯ A) → is-local (B x)) (η* : Π A (B ∘ η)) where

      f = ◯-elim B-local η*
      η-β = ◯-elim-β B-local η*

    module ◯Rec {A : Type ℓ} {B : Type ℓ}
      (B-local : is-local B) (η* : A → B)
      = ◯Elim (λ _ → B-local) η*
    ◯-rec = ◯Rec.f
    ◯-rec-β = ◯Rec.η-β

    {- functoriality -}

    module ◯Fmap {A B : Type ℓ} (f : A → B) =
      ◯Rec ◯-is-local (η ∘ f)
    ◯-fmap = ◯Fmap.f
    ◯-fmap-β = ◯Fmap.η-β

    ◯-isemap : {A B : Type ℓ} (f : A → B) → is-equiv f → is-equiv (◯-fmap f)
    ◯-isemap f f-ise = is-eq _ (◯-fmap g) to-from from-to where
      open is-equiv f-ise
      abstract
        to-from : ∀ ◯b → ◯-fmap f (◯-fmap g ◯b) == ◯b
        to-from = ◯-elim
          (λ ◯b → ◯-=-is-local (◯-fmap f (◯-fmap g ◯b)) ◯b)
          (λ b → ap (◯-fmap f) (◯-fmap-β g b) ∙ ◯-fmap-β f (g b) ∙ ap η (f-g b))
        from-to : ∀ ◯a → ◯-fmap g (◯-fmap f ◯a) == ◯a
        from-to = ◯-elim
          (λ ◯a → ◯-=-is-local (◯-fmap g (◯-fmap f ◯a)) ◯a)
          (λ a → ap (◯-fmap g) (◯-fmap-β f a) ∙ ◯-fmap-β g (f a) ∙ ap η (g-f a))

    ◯-emap : {A B : Type ℓ} → A ≃ B → ◯ A ≃ ◯ B
    ◯-emap (f , f-ise) = ◯-fmap f , ◯-isemap f f-ise

    {- equivalences preserve locality -}


    -- This is the only appearence of univalence, but ...
    local-is-replete : {A B : Type ℓ} → is-local A → A ≃ B → is-local B
    local-is-replete w eq = transport is-local (ua eq) w

    -- This name aligns with the current codebase better.
    equiv-preserves-local : {A B : Type ℓ} → A ≃ B → is-local A → is-local B
    equiv-preserves-local e A-is-loc = local-is-replete A-is-loc e

    {- locality and [η] being an equivalence -}

    local-implies-η-equiv : {A : Type ℓ} → is-local A → is-equiv (η {A})
    local-implies-η-equiv {A} w = is-eq (η {A}) η-inv inv-l inv-r

       where η-inv : ◯ A → A
             η-inv = ◯-rec w (idf A)

             abstract
               inv-r : (a : A) → η-inv (η a) == a
               inv-r = ◯-rec-β w (idf A)

               inv-l : (a : ◯ A) → η (η-inv a) == a
               inv-l = ◯-elim (λ a₀ → ◯-=-is-local _ _)
                              (λ a₀ → ap η (inv-r a₀))

    abstract
      η-equiv-implies-local : {A : Type ℓ} → is-equiv (η {A}) → is-local A
      η-equiv-implies-local {A} eq = local-is-replete {◯ A} {A} ◯-is-local ((η , eq) ⁻¹)

      retract-is-local : {A B : Type ℓ} (w : is-local A)
        (f : A → B) (g : B → A) (r : (b : B) → f (g b) == b) →
        is-local B
      retract-is-local {A} {B} w f g r = η-equiv-implies-local (is-eq η η-inv inv-l inv-r)

        where η-inv : ◯ B → B
              η-inv = f ∘ (◯-rec w g)

              inv-r : (b : B) → η-inv (η b) == b
              inv-r b = ap f (◯-rec-β w g b) ∙ r b

              inv-l : (b : ◯ B) → η (η-inv b) == b
              inv-l = ◯-elim (λ b → ◯-=-is-local _ _) (λ b → ap η (inv-r b))

    {- locality of identification -}

    abstract
      =-preserves-local : {A : Type ℓ} → is-local A → {a₀ a₁ : A} → is-local (a₀ == a₁)
      =-preserves-local {A} w {a₀} {a₁} = local-is-replete
        (◯-=-is-local (η a₀) (η a₁)) (ap-equiv (η , local-implies-η-equiv w) a₀ a₁ ⁻¹)

  {- ◯-connectness and ◯-equivalences -}

    is-◯-connected : Type ℓ → Type ℓ
    is-◯-connected A = is-contr (◯ A)

    is-◯-connected-is-prop : ∀ {A} → is-prop (is-◯-connected A)
    is-◯-connected-is-prop {A} = is-contr-is-prop
    
    is-◯-equiv : {A B : Type ℓ} → (A → B) → Type ℓ
    is-◯-equiv {B = B} f = (b : B) → is-◯-connected (hfiber f b)

    has-◯-conn-fibers = is-◯-equiv

    is-lex : Type (lsucc ℓ)
    is-lex = {A B : Type ℓ} (f : A → B)
      → is-◯-connected A → is-◯-connected B → is-◯-equiv f

    equiv-preserves-◯-conn : {A B : Type ℓ} → A ≃ B → is-◯-connected A → is-◯-connected B
    equiv-preserves-◯-conn e c = equiv-preserves-level (◯-emap e) c

    total-◯-equiv : {A : Type ℓ} {P Q : A → Type ℓ} (φ : ∀ a → P a → Q a) → 
                     (∀ a → is-◯-equiv (φ a)) → is-◯-equiv (Σ-fmap-r φ)
    total-◯-equiv φ e (a , q) = equiv-preserves-◯-conn (hfiber-Σ-fmap-r φ q ⁻¹) (e a q)

    module _ {A B : Type ℓ} {h : A → B} (c : is-◯-equiv h) (P : B → ◯-Type) where
      abstract
        pre∘-◯-conn-is-equiv : is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h)
        pre∘-◯-conn-is-equiv = is-eq f g f-g g-f

          where f : Π B (fst ∘ P) → Π A (fst ∘ P ∘ h)
                f k a = k (h a)

                helper : Π A (fst ∘ P ∘ h) → (b : B) → ◯ (Σ A (λ a → h a == b)) → (fst (P b))
                helper t b = ◯-rec (snd (P b)) (λ x → transport (fst ∘ P) (snd x) (t (fst x)))

                helper-β : (t : Π A (fst ∘ P ∘ h)) → (b : B) → (r : hfiber h b) →
                           helper t b (η r) == transport (fst ∘ P) (snd r) (t (fst r))
                helper-β t b = ◯-rec-β (snd (P b)) (λ x → transport (fst ∘ P) (snd x) (t (fst x)))

                g : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
                g t b = helper t b (fst (c b))

                f-g : ∀ t → f (g t) == t
                f-g t = λ= $ λ a → transport
                  (λ r → ◯-rec (snd (P (h a))) _ r == t a)
                  (! (snd (c (h a)) (η (a , idp))))
                  (◯-rec-β (snd (P (h a))) _ (a , idp))

                g-f : ∀ k → g (f k) == k
                g-f k = λ= λ (b : B) →
                  ◯-elim {A = hfiber h b}
                         (λ r → =-preserves-local (snd (P b)) {g (f k) b})
                         (λ r → lemma₁ (fst r) b (snd r))
                         (fst (c b))

                    where lemma₀ : (a : A) → (b : B) → (p : h a == b) →
                                 helper (k ∘ h) b (η (a , p)) == k b
                          lemma₀ a .(h a) idp = helper-β (k ∘ h) (h a) (a , idp)

                          lemma₁ : (a : A) → (b : B) → (p : h a == b) →
                                 helper (k ∘ h) b (fst (c b)) == k b
                          lemma₁ a b p = transport! (λ r → helper (k ∘ h) b r == k b)
                            (snd (c b) (η (a , p))) (lemma₀ a b p)

      ◯-extend : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
      ◯-extend = is-equiv.g pre∘-◯-conn-is-equiv

      ◯-extend-β : ∀ f a → ◯-extend f (h a) == f a
      ◯-extend-β f = app= (is-equiv.f-g pre∘-◯-conn-is-equiv f)

    {- locality of function types -}

    abstract
      Π-is-local : {A : Type ℓ} {B : A → Type ℓ} (w : (a : A) → is-local (B a)) → is-local (Π A B)
      Π-is-local {A} {B} w = retract-is-local {◯ (Π A B)} {Π A B} ◯-is-local η-inv η r

        where η-inv : ◯ (Π A B) → Π A B
              η-inv φ' a = ◯-rec (w a) (λ φ → φ a) φ'

              r : (φ : Π A B) → η-inv (η φ) == φ
              r φ = λ= (λ a → ◯-rec-β (w a) (λ φ₀ → φ₀ a) φ)

      →-is-local : {A B : Type ℓ} → is-local B → is-local (A → B)
      →-is-local w = Π-is-local (λ _ → w)

    -- Fmap2 because of locality of function types
    module ◯Fmap2 {A B C : Type ℓ} (η* : A → B → C) where
      private module M = ◯Rec (→-is-local ◯-is-local) (◯-fmap ∘ η*)
      f = M.f
      η-β : ∀ a b → f (η a) (η b) == η (η* a b)
      η-β a b = app= (M.η-β a) (η b) ∙ ◯-fmap-β (η* a) b
    ◯-fmap2 = ◯Fmap2.f
    ◯-fmap2-β = ◯Fmap2.η-β

    {- locality of sigma types -}

    abstract
      Σ-is-local : {A : Type ℓ} (B : A → Type ℓ)
        → is-local A → ((a : A) → is-local (B a))
        → is-local (Σ A B)
      Σ-is-local {A} B lA lB = retract-is-local {◯ (Σ A B)} {Σ A B} ◯-is-local η-inv η r

        where h : ◯ (Σ A B) → A
              h = ◯-rec lA fst

              h-β : (ab : Σ A B) → h (η ab) == fst ab
              h-β = ◯-rec-β lA fst

              k : (w : ◯ (Σ A B)) → B (h w)
              k = ◯-elim (lB ∘ h) λ ab → transport! B (h-β ab) (snd ab)

              k-β : (ab : Σ A B) → k (η ab) == snd ab [ B ↓ h-β ab ]
              k-β ab = from-transp! B (h-β ab) $
                ◯-elim-β (lB ∘ h) (λ ab → transport! B (h-β ab) (snd ab)) ab

              η-inv : ◯ (Σ A B) → Σ A B
              η-inv w = h w , k w

              r : (x : Σ A B) → η-inv (η x) == x
              r ab = pair= (h-β ab) (k-β ab)

      ×-is-local : {A B : Type ℓ}
        → is-local A → is-local B → is-local (A × B)
      ×-is-local {B = B} lA lB = Σ-is-local (λ _ → B) lA (λ _ → lB)

    ◯-×-econv : {A B : Type ℓ} → ◯ (A × B) ≃ ◯ A × ◯ B
    ◯-×-econv {A} {B} = equiv ◯-split ◯-pair inv-l inv-r

      where ◯-fst : ◯ (A × B) → ◯ A
            ◯-fst = ◯-fmap fst

            ◯-fst-β : (ab : A × B) → ◯-fst (η ab) == η (fst ab)
            ◯-fst-β = ◯-fmap-β fst

            ◯-snd : ◯ (A × B) → ◯ B
            ◯-snd = ◯-fmap snd

            ◯-snd-β : (ab : A × B) → ◯-snd (η ab) == η (snd ab)
            ◯-snd-β = ◯-fmap-β snd

            ◯-split : ◯ (A × B) → ◯ A × ◯ B
            ◯-split = fanout ◯-fst ◯-snd

            ◯-pair : ◯ A × ◯ B → ◯ (A × B)
            ◯-pair = uncurry (◯-fmap2 _,_)

            ◯-pair-β : (a : A) (b : B) → ◯-pair (η a , η b) == η (a , b)
            ◯-pair-β = ◯-fmap2-β _,_

            abstract
              inv-l : (ab : ◯ A × ◯ B) → ◯-split (◯-pair ab) == ab
              inv-l = uncurry $
                ◯-elim (λ _ → Π-is-local λ _ → =-preserves-local (×-is-local ◯-is-local ◯-is-local))
                  (λ a → ◯-elim (λ _ → =-preserves-local (×-is-local ◯-is-local ◯-is-local))
                    (λ b → ap ◯-split (◯-pair-β a b)
                         ∙ pair×= (◯-fst-β (a , b)) (◯-snd-β (a , b))))

              inv-r : (ab : ◯ (A × B)) → ◯-pair (◯-split ab) == ab
              inv-r = ◯-elim (λ _ → ◯-=-is-local _ _)
                             (λ ab → ap ◯-pair (pair×= (◯-fst-β ab) (◯-snd-β ab)) ∙ ◯-pair-β (fst ab) (snd ab))

