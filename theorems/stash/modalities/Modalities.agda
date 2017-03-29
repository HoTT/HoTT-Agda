{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.Modalities where

  record Modality {ℓ} : Type (lsucc ℓ) where
    field

      is-local : Type ℓ → Type ℓ
      is-local-is-prop : {A : Type ℓ} → is-prop (is-local A)

      ◯ : Type ℓ → Type ℓ
      ◯-is-local : {A : Type ℓ} → is-local (◯ A)      

      η : {A : Type ℓ} → A → ◯ A

      ◯-elim : {A : Type ℓ} (B : ◯ A → Type ℓ) (B-local : Π (◯ A) (λ a → is-local (B a)))
                → Π A (B ∘ η) → Π (◯ A) B

      ◯-elim-β : {A : Type ℓ} (B : ◯ A → Type ℓ) (B-local : Π (◯ A) (λ a → is-local (B a))) (f : Π A (B ∘ η))
                  → (a : A) → ◯-elim B B-local f (η a) == f a
                  
      ◯-== : {A : Type ℓ} (a₀ a₁ : ◯ A) → is-local (a₀ == a₁)

  module _ {ℓ} (M : Modality {ℓ}) where

    open Modality M

    ◯-Type : Type (lsucc ℓ)
    ◯-Type = Σ (Type ℓ) is-local

    is-◯-connected : Type ℓ → Type ℓ
    is-◯-connected A = is-contr (◯ A)

    is-◯-equiv : {A B : Type ℓ} → (A → B) → Type ℓ
    is-◯-equiv {B = B} f = (b : B) → is-◯-connected (hfiber f b)
    
    is-lex : Type (lsucc ℓ)
    is-lex = (A : Type ℓ) → (B : Type ℓ) → (f : A → B) →
             is-◯-connected A → is-◯-connected B →
             (b : B) → is-◯-connected (hfiber f b)
    
    -- Some basic constructions

    ◯-rec : {A B : Type ℓ} (w : is-local B) (f : A → B) → ◯ A → B
    ◯-rec {A} {B} w f = ◯-elim (λ _ → B) (λ _ → w) f

    ◯-rec-β : {A B : Type ℓ} (w : is-local B) (f : A → B) (a : A) → ◯-rec w f (η a) == f a
    ◯-rec-β {A} {B} w f a = ◯-elim-β _ _ f a

    ◯-func : {A B : Type ℓ} (f : A → B) → ◯ A → ◯ B
    ◯-func {A} {B} f = ◯-rec ◯-is-local (λ a → η (f a))

    -- This is the only appearence of univalence, but ...
    is-local-is-replete : {A B : Type ℓ} → is-local A → A ≃ B → is-local B
    is-local-is-replete w eq = transport is-local (ua eq) w

    is-local-to-η-equiv : {A : Type ℓ} → is-local A → is-equiv (η {A})
    is-local-to-η-equiv {A} w = is-eq (η {A}) η-inv inv-l inv-r 

       where η-inv : ◯ A → A
             η-inv = ◯-rec w (idf A)

             inv-r : (a : A) → η-inv (η a) == a
             inv-r = ◯-rec-β w (idf A)

             inv-l : (a : ◯ A) → η (η-inv a) == a
             inv-l = ◯-elim (λ a₀ → η (η-inv a₀) == a₀)
                             (λ a₀ → ◯-== _ _)
                             (λ a₀ → ap η (inv-r a₀))

    is-local-from-η-equiv : {A : Type ℓ} → is-equiv (η {A}) → is-local A
    is-local-from-η-equiv {A} eq = is-local-is-replete {◯ A} {A} ◯-is-local ((η , eq) ⁻¹)

    is-local-retract : {A B : Type ℓ} (w : is-local A)
                       (f : A → B) (g : B → A) (r : (b : B) → f (g b) == b) →
                       is-local B
    is-local-retract {A} {B} w f g r = is-local-from-η-equiv {B} (is-eq η η-inv inv-l inv-r)

      where η-inv : ◯ B → B
            η-inv = f ∘ (◯-rec w g)

            inv-r : (b : B) → η-inv (η b) == b
            inv-r b = ap f (◯-rec-β w g b) ∙ r b

            inv-l : (b : ◯ B) → η (η-inv b) == b
            inv-l = ◯-elim _ (λ b → ◯-== _ _) (λ b → ap η (inv-r b))

    ==-is-local : {A : Type ℓ} {a₀ a₁ : A} → is-local A → is-local (a₀ == a₁)
    ==-is-local {A} {a₀} {a₁} w  = is-local-is-replete
      (◯-== (η a₀) (η a₁)) (ap-equiv (η , is-local-to-η-equiv w) a₀ a₁ ⁻¹)

    Π-is-local : {A : Type ℓ} (B : A → Type ℓ) (w : (a : A) → is-local (B a)) → is-local (Π A B)
    Π-is-local {A} B w = is-local-retract {◯ (Π A B)} {Π A B} ◯-is-local η-inv η r

      where η-inv : ◯ (Π A B) → Π A B
            η-inv φ' a = ◯-rec (w a) (λ φ → φ a) φ'

            r : (φ : Π A B) → η-inv (η φ) == φ
            r φ = λ= (λ a → ◯-rec-β (w a) (λ φ₀ → φ₀ a) φ)
    
    -- Σ-P : {A : Type ℓ} (B : A → Type ℓ) (pA : P A) (pB : (a : A) → P (B a)) → P (Σ A B)
    -- Σ-P {A} B pA pB = ◯-retract {◯ (Σ A B)} {Σ A B} in-◯ η-inv η {!!}

    --   where h : ◯ (Σ A B) → A
    --         h = (is-equiv.g (P-η-equiv pA)) ∘ (◯-func fst)
            
    --         C : ◯ (Σ A B) → Type ℓ
    --         C w = B (h w)

    --         η-inv : ◯ (Σ A B) → Σ A B
    --         η-inv w = h w , {!!}

    abstract
      pre∘-◯-conn-is-equiv : {A B : Type ℓ} {h : A → B} → is-◯-equiv h → 
                             (P : B → ◯-Type) → is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h)
      pre∘-◯-conn-is-equiv {A} {B} {h} c P = is-eq f g f-g g-f                               

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
              g-f k = λ= $ λ (b : B) →
                ◯-elim {A = hfiber h b}
                        (λ _ → g (f k) b == k b)
                        (λ r → ==-is-local (snd (P b)))
                        (λ r → lemma₁ (fst r) b (snd r))
                        (fst (c b))

                  where lemma₀ : (a : A) → (b : B) → (p : h a == b) →
                               helper (k ∘ h) b (η (a , p)) == k b
                        lemma₀ a .(h a) idp = helper-β (k ∘ h) (h a) (a , idp) 

                        lemma₁ : (a : A) → (b : B) → (p : h a == b) →
                               helper (k ∘ h) b (fst (c b)) == k b
                        lemma₁ a b p = transport! (λ r → helper (k ∘ h) b r == k b)
                          (snd (c b) (η (a , p))) (lemma₀ a b p)


    ◯-connected-elim : {A B : Type ℓ} (f : A → B) → is-◯-equiv f →
                        (P : B → ◯-Type) → Π A (fst ∘ P ∘ f) → Π B (fst ∘ P)
    ◯-connected-elim f c P s = is-equiv.g (pre∘-◯-conn-is-equiv {h = f} c P) s

    ◯-preserves-× : {A B : Type ℓ} → ◯ (A × B) ≃ ◯ A × ◯ B
    ◯-preserves-× {A} {B} = equiv ◯-split ◯-pair inv-l inv-r

      where ◯-fst : ◯ (A × B) → ◯ A
            ◯-fst ab = ◯-func fst ab

            ◯-fst-β : (ab : A × B) → ◯-fst (η ab) == η (fst ab)
            ◯-fst-β ab = ◯-rec-β ◯-is-local _ ab
            
            ◯-snd : ◯ (A × B) → ◯ B
            ◯-snd ab = ◯-func snd ab

            ◯-snd-β : (ab : A × B) → ◯-snd (η ab) == η (snd ab)
            ◯-snd-β ab = ◯-rec-β ◯-is-local _ ab

            ◯-split : ◯ (A × B) → ◯ A × ◯ B
            ◯-split ab = (◯-fst ab , ◯-snd ab)
            
            ◯-pair : ◯ A × ◯ B → ◯ (A × B)
            ◯-pair (a , b) = ◯-rec (Π-is-local _ (λ _ → ◯-is-local)) (λ a₀ → ◯-rec ◯-is-local (λ b₀ → η (a₀ , b₀))) a b

            ◯-pair-β : (a : A) → (b : B) → ◯-pair (η a , η b) == η (a , b)
            ◯-pair-β a b = ◯-rec (Π-is-local _ (λ _ → ◯-is-local)) (λ a₀ → ◯-rec ◯-is-local (λ b₀ → η (a₀ , b₀))) (η a) (η b)
                              =⟨ ◯-rec-β _ (λ a₀ → ◯-rec ◯-is-local (λ b₀ → η (a₀ , b₀))) a |in-ctx (λ x → x (η b)) ⟩
                            ◯-rec ◯-is-local (λ b₀ → η (a , b₀)) (η b)
                              =⟨ ◯-rec-β _ _ b ⟩ 
                            η (a , b) ∎

            lem₀ : (a : ◯ A) → (b : ◯ B) → ◯-fst (◯-pair (a , b)) == a
            lem₀ = ◯-elim _ (λ _ → Π-is-local _ (λ _ → ◯-== _ _))
                             (λ a → ◯-elim _ (λ _ → ◯-== _ _)
                             (λ b → ap ◯-fst (◯-pair-β a b) ∙ ◯-fst-β (a , b)))

            lem₁ : (a : ◯ A) → (b : ◯ B) → ◯-snd (◯-pair (a , b)) == b
            lem₁ = ◯-elim _ (λ _ → Π-is-local _ (λ _ → ◯-== _ _))
                             (λ a → ◯-elim _ (λ _ → ◯-== _ _)
                             (λ b → ap ◯-snd (◯-pair-β a b) ∙ ◯-snd-β (a , b)))

            inv-l : (ab : ◯ A × ◯ B) → ◯-split (◯-pair ab) == ab
            inv-l (a , b) = pair×= (lem₀ a b) (lem₁ a b)

            inv-r : (ab : ◯ (A × B)) → ◯-pair (◯-split ab) == ab
            inv-r = ◯-elim _ (λ _ → ◯-== _ _)
                             (λ ab → ap ◯-pair (pair×= (◯-fst-β ab) (◯-snd-β ab)) ∙ ◯-pair-β (fst ab) (snd ab))

