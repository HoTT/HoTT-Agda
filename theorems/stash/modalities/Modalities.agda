{-# OPTIONS --without-K #-}

open import HoTT

module stash.modalities.Modalities where

  record Modality {ℓ} : Type (lsucc ℓ) where
    field

      P : Type ℓ → Type ℓ
      P-is-prop : {A : Type ℓ} → is-prop (P A)

      ◯ : Type ℓ → Type ℓ
      in-◯ : {A : Type ℓ} → P (◯ A)      

      η : {A : Type ℓ} → A → ◯ A

      ◯-elim : {A : Type ℓ} (B : ◯ A → Type ℓ) (B-in : Π (◯ A) (λ a → P (B a)))
                → Π A (B ∘ η) → Π (◯ A) B

      ◯-elim-β : {A : Type ℓ} (B : ◯ A → Type ℓ) (B-in : Π (◯ A) (λ a → P (B a))) (f : Π A (B ∘ η))
                  → (a : A) → ◯-elim B B-in f (η a) == f a
                  
      ◯-== : {A : Type ℓ} (a₀ a₁ : ◯ A) → P (a₀ == a₁)

  module _ {ℓ} (M : Modality {ℓ}) where

    open Modality M

    P-Type : Type (lsucc ℓ)
    P-Type = Σ (Type ℓ) P

    is-conn : Type ℓ → Type ℓ
    is-conn A = is-contr (◯ A)

    is-lex : Type (lsucc ℓ)
    is-lex = (A : Type ℓ) → (B : Type ℓ) → (f : A → B) →
                    is-conn A → is-conn B → (b : B) → is-conn (hfiber f b)

    -- Some basic constructions

    ◯-rec : {A B : Type ℓ} (w : P B) (f : A → B) → ◯ A → B
    ◯-rec {A} {B} w f = ◯-elim (λ _ → B) (λ _ → w) f

    ◯-rec-β : {A B : Type ℓ} (w : P B) (f : A → B) (a : A) → ◯-rec w f (η a) == f a
    ◯-rec-β {A} {B} w f a = ◯-elim-β _ _ f a

    ◯-func : {A B : Type ℓ} (f : A → B) → ◯ A → ◯ B
    ◯-func {A} {B} f = ◯-rec in-◯ (λ a → η (f a))

    -- This is the only appearence of univalence, but ...
    P-replete : {A B : Type ℓ} → P A → A ≃ B → P B
    P-replete w eq = transport P (ua eq) w

    P-η-equiv : {A : Type ℓ} → P A → is-equiv (η {A})
    P-η-equiv {A} w = is-eq (η {A}) η-inv inv-l inv-r

      where η-inv : ◯ A → A
            η-inv = ◯-rec w (idf A)

            inv-r : (a : A) → η-inv (η a) == a
            inv-r = ◯-rec-β w (idf A)

            inv-l : (a : ◯ A) → η (η-inv a) == a
            inv-l = ◯-elim (λ a₀ → η (η-inv a₀) == a₀)
                            (λ a₀ → ◯-== _ _)
                            (λ a₀ → ap η (inv-r a₀))

    P-η-equiv-inv : {A : Type ℓ} → is-equiv (η {A}) → P A
    P-η-equiv-inv {A} eq = P-replete {◯ A} {A} in-◯ ((η , eq) ⁻¹)

    ◯-retract : {A B : Type ℓ} (w : P A) (f : A → B) (g : B → A) (linv : (b : B) → f (g b) == b) → P B
    ◯-retract {A} {B} w f g linv = P-η-equiv-inv {B} (is-eq η η-inv inv-l inv-r)

      where η-inv : ◯ B → B
            η-inv = f ∘ (◯-rec w g)

            inv-r : (b : B) → η-inv (η b) == b
            inv-r b = ap f (◯-rec-β w g b) ∙ linv b

            inv-l : (b : ◯ B) → η (η-inv b) == b
            inv-l = ◯-elim _ (λ b → ◯-== _ _) (λ b → ap η (inv-r b))

    Π-P : {A : Type ℓ} (B : A → Type ℓ) (w : (a : A) → P (B a)) → P (Π A B)
    Π-P {A} B w = ◯-retract {◯ (Π A B)} {Π A B} in-◯ η-inv η retract

      where η-inv : ◯ (Π A B) → Π A B
            η-inv φ' a = ◯-rec (w a) (λ φ → φ a) φ'

            retract : (φ : Π A B) → η-inv (η φ) == φ
            retract φ = λ= (λ a → ◯-rec-β (w a) (λ φ₀ → φ₀ a) φ)

    
    -- Σ-P : {A : Type ℓ} (B : A → Type ℓ) (pA : P A) (pB : (a : A) → P (B a)) → P (Σ A B)
    -- Σ-P {A} B pA pB = ◯-retract {◯ (Σ A B)} {Σ A B} in-◯ η-inv η {!!}

    --   where h : ◯ (Σ A B) → A
    --         h = (is-equiv.g (P-η-equiv pA)) ∘ (◯-func fst)
            
    --         C : ◯ (Σ A B) → Type ℓ
    --         C w = B (h w)

    --         η-inv : ◯ (Σ A B) → Σ A B
    --         η-inv w = h w , {!!}


    ◯-preserves-× : {A B : Type ℓ} → ◯ (A × B) ≃ ◯ A × ◯ B
    ◯-preserves-× {A} {B} = equiv ◯-split ◯-pair inv-l inv-r

      where ◯-fst : ◯ (A × B) → ◯ A
            ◯-fst ab = ◯-func fst ab

            ◯-fst-β : (ab : A × B) → ◯-fst (η ab) == η (fst ab)
            ◯-fst-β ab = ◯-rec-β in-◯ _ ab
            
            ◯-snd : ◯ (A × B) → ◯ B
            ◯-snd ab = ◯-func snd ab

            ◯-snd-β : (ab : A × B) → ◯-snd (η ab) == η (snd ab)
            ◯-snd-β ab = ◯-rec-β in-◯ _ ab

            ◯-split : ◯ (A × B) → ◯ A × ◯ B
            ◯-split ab = (◯-fst ab , ◯-snd ab)
            
            ◯-pair : ◯ A × ◯ B → ◯ (A × B)
            ◯-pair (a , b) = ◯-rec (Π-P _ (λ _ → in-◯)) (λ a₀ → ◯-rec in-◯ (λ b₀ → η (a₀ , b₀))) a b

            ◯-pair-β : (a : A) → (b : B) → ◯-pair (η a , η b) == η (a , b)
            ◯-pair-β a b = ◯-rec (Π-P _ (λ _ → in-◯)) (λ a₀ → ◯-rec in-◯ (λ b₀ → η (a₀ , b₀))) (η a) (η b)
                              =⟨ ◯-rec-β _ (λ a₀ → ◯-rec in-◯ (λ b₀ → η (a₀ , b₀))) a |in-ctx (λ x → x (η b)) ⟩
                            ◯-rec in-◯ (λ b₀ → η (a , b₀)) (η b)
                              =⟨ ◯-rec-β _ _ b ⟩ 
                            η (a , b) ∎

            lem₀ : (a : ◯ A) → (b : ◯ B) → ◯-fst (◯-pair (a , b)) == a
            lem₀ = ◯-elim _ (λ _ → Π-P _ (λ _ → ◯-== _ _))
                             (λ a → ◯-elim _ (λ _ → ◯-== _ _)
                             (λ b → ap ◯-fst (◯-pair-β a b) ∙ ◯-fst-β (a , b)))

            lem₁ : (a : ◯ A) → (b : ◯ B) → ◯-snd (◯-pair (a , b)) == b
            lem₁ = ◯-elim _ (λ _ → Π-P _ (λ _ → ◯-== _ _))
                             (λ a → ◯-elim _ (λ _ → ◯-== _ _)
                             (λ b → ap ◯-snd (◯-pair-β a b) ∙ ◯-snd-β (a , b)))

            inv-l : (ab : ◯ A × ◯ B) → ◯-split (◯-pair ab) == ab
            inv-l (a , b) = pair×= (lem₀ a b) (lem₁ a b)

            inv-r : (ab : ◯ (A × B)) → ◯-pair (◯-split ab) == ab
            inv-r = ◯-elim _ (λ _ → ◯-== _ _)
                             (λ ab → ap ◯-pair (pair×= (◯-fst-β ab) (◯-snd-β ab)) ∙ ◯-pair-β (fst ab) (snd ab))

    -- module _ {ℓ} (Q : Type ℓ) (Q-prop : is-prop Q) where

    --   ● : Type ℓ → Type ℓ
    --   ● A = Q * A

    --   η-● : {A : Type ℓ} → A → ● A
    --   η-● a = right a

    --   -- Idea: When Q is a proposition, the type Q * A is
    --   -- a model for the nullification with respect to Q!

    --   -- But can this be true?  Because I don't see that, for example,
    --   -- Q * Q is always contractible.  Whereas the nullification of
    --   -- the "parameter" should always be contractible, no?

    --   -- Yeah, I don't think that's right.
      
    --   -- η-●-inv : {A : Type ℓ} → ● (● A) → ● A
    --   η-●-inv : {A : Type ℓ} → Q * (Q * A) → Q * A
    --   η-●-inv {A} = PushoutRec.f left (idf (Q * A)) (λ { (q , qa) → pth q qa})

    --     where pth : (q : Q) → (qa : Q * A) → left q == qa
    --           pth q = Pushout-elim (λ q₀ → ap left (prop-has-all-paths Q-prop q q₀))
    --                                (λ a → glue (q , a))
    --                                (λ { (q₀ , a) → finally q₀ a })

    --                     where finally : (q₀ : Q) → (a : A) → ap left (prop-has-all-paths Q-prop q q₀) == glue (q , a) [ (λ z → left q == z) ↓ glue (q₀ , a) ]
    --                           finally = {!!}

    --   lemma : {A : Type ℓ} → is-equiv (η-● {● A})
    --   lemma {A} = {!!}

    --   thm : {A : Type ℓ} → Q * A ≃ Q * (Q * A)
    --   thm {A} = η-● {● A} , lemma

    --   -- This is the closed modality associated to a proposition.
    --   ClosedModality : Modality {ℓ}
    --   Modality.P ClosedModality A = is-equiv (η-● {A})
    --   Modality.P-is-prop ClosedModality {A} = is-equiv-is-prop (η-● {A})
    --   Modality.◯ ClosedModality = ●
    --   Modality.in-◯ ClosedModality = lemma
    --   Modality.η ClosedModality = η-●
    --   Modality.◯-elim ClosedModality B B-in x x₁ = {!!}
    --   Modality.◯-elim-β ClosedModality B B-in f a = {!!}
    --   Modality.◯-== ClosedModality a₀ a₁ = {!!}


