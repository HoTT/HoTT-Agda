{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.SmashFmapConn where

module _ {i} {j} (S* : Type i) (P* : S* → Type j) where

  foo : {s₁ s₂ t : S*} (p* : P* s₂) (p₁ : s₁ == t) (p₂ : s₂ == t)
    → transport P* (! (p₁ ∙ ! p₂)) p*  == transport P* p₂ p* [ P* ↓ p₁ ]
  foo p* p₁@idp p₂@idp = idp

  bar : ∀ {k} {C : Type k} (f : C → S*)
    {c₁ c₂ : C} (q : c₁ == c₂)
    {t : S*} (d : Π C (P* ∘ f))
    (p₁ : f c₁ == t) (p₂ : f c₂ == t)
    (r : ap f q == p₁ ∙' ! p₂)
    {u  : P* (f c₂)} (v  : u  == transport P* (! (p₂ ∙ ! p₂)) (d c₂))
    {u' : P* (f c₁)} (v' : u' == transport P* (! (p₁ ∙ ! p₂)) (d c₂))
    → (v' ∙
       ap (λ pp → transport P* pp (d c₂)) (ap ! (! (r ∙ ∙'=∙ p₁ (! p₂))) ∙ !-ap f q) ∙
       to-transp {B = P*} {p = ap f (! q)}
                 (↓-ap-in P* f (apd d (! q)))) ◃
      apd d q
      ==
      ↓-ap-out= P* f q (r ∙ ∙'=∙ p₁ (! p₂))
                ((v' ◃ foo (d c₂) p₁ p₂) ∙ᵈ !ᵈ (v ◃ foo (d c₂) p₂ p₂)) ▹
      (v ∙ ap (λ pp → transport P* (! pp) (d c₂)) (!-inv-r p₂))
  bar f q@idp d p₁@.idp p₂@idp r@idp v@idp v'@idp = idp

module _ {i} {j} {k} {A : Ptd i} {A' : Ptd j} (f : A ⊙→ A') (B : Ptd k)
         {m n : ℕ₋₂}
         (f-is-m-conn : has-conn-fibers m (fst f))
         (B-is-Sn-conn : is-connected (S n) (de⊙ B)) where

  private
    a₀ = pt A
    a₀' = pt A'
    b₀ = pt B

  module ConnIn (P : A' ∧ B → (m +2+ n) -Type (lmax i (lmax j k)))
                (d : ∀ (ab : A ∧ B) → fst (P (∧-fmap f (⊙idf B) ab))) where

    h : ∀ (b : de⊙ B)
      → (∀ (a' : de⊙ A') → fst (P (smin a' b)))
      → (∀ (a : de⊙ A) → fst (P (smin (fst f a) b)))
    h b s = s ∘ fst f

    Q : de⊙ B → n -Type (lmax i (lmax j k))
    Q b = hfiber (h b) (λ a → d (smin a b)) , {!!}

    s₀ : ∀ (a' : de⊙ A') → fst (P (smin a' b₀))
    s₀ a' = transport (fst ∘ P) (! (∧-norm-l a')) (d smbasel)

    ∧-fmap-smgluel-β-∙' : ∀ (a : de⊙ A) →
      ap (∧-fmap f (⊙idf B)) (smgluel a)
      ==
      smgluel (fst f a) ∙' ! (smgluel a₀')
    ∧-fmap-smgluel-β-∙' a =
      ∧-fmap-smgluel-β' f (⊙idf B) a ∙
      ∙=∙' (smgluel (fst f a)) (! (smgluel a₀'))

    ∧-fmap-smgluel-β-∙ : ∀ (a : de⊙ A) →
      ap (∧-fmap f (⊙idf B)) (smgluel a)
      ==
      smgluel (fst f a) ∙ ! (smgluel a₀')
    ∧-fmap-smgluel-β-∙ a =
      ∧-fmap-smgluel-β-∙' a ∙
      ∙'=∙ (smgluel (fst f a)) (! (smgluel a₀'))

    s₀-f : ∀ (a : de⊙ A) → s₀ (fst f a) == d (smin a b₀)
    s₀-f a =
      ap (λ p → transport (λ a'b → fst (P a'b)) p (d smbasel)) q ∙
      to-transp {B = fst ∘ P}
                {p = ap (∧-fmap f (⊙idf B)) (! (smgluel a))}
                (↓-ap-in (fst ∘ P)
                         (∧-fmap f (⊙idf B))
                         (apd d (! (smgluel a))))
      where
      q : ! (∧-norm-l (fst f a)) == ap (∧-fmap f (⊙idf B)) (! (smgluel a))
      q = ap ! (! (∧-fmap-smgluel-β-∙ a)) ∙ !-ap (∧-fmap f (⊙idf B)) (smgluel a)

    q₀ : fst (Q b₀)
    q₀ = s₀ , s₀-lies-over-pt
      where
      s₀-lies-over-pt : h b₀ s₀ == (λ a → d (smin a b₀))
      s₀-lies-over-pt = λ= s₀-f

    q : ∀ (b : de⊙ B) → fst (Q b)
    q = conn-extend {n = n} {h = cst b₀}
                    (pointed-conn-out (de⊙ B) b₀ {{B-is-Sn-conn}})
                    Q
                    (λ _ → q₀)

    q-f : q b₀ == q₀
    q-f = conn-extend-β {n = n} {h = cst b₀}
                        (pointed-conn-out (de⊙ B) b₀ {{B-is-Sn-conn}})
                        Q
                        (λ _ → q₀)
                        unit

    s : ∀ (a' : de⊙ A') (b : de⊙ B) → fst (P (smin a' b))
    s a' b = fst (q b) a'

    s-b₀ : ∀ (a' : de⊙ A') → s a' b₀ == s₀ a'
    s-b₀ a' = ap (λ u → fst u a') q-f

    s-a₀'-b₀ : s a₀' b₀ =-= d smbasel
    s-a₀'-b₀ =
      s a₀' b₀
        =⟪ s-b₀ a₀' ⟫
      s₀ a₀'
        =⟪idp⟫
      transport (fst ∘ P) (! (∧-norm-l a₀')) (d smbasel)
        =⟪ ap (λ p → transport (fst ∘ P) (! p) (d smbasel))
              (!-inv-r (smgluel a₀')) ⟫
      d smbasel ∎∎

    s-f : ∀ (a : de⊙ A) (b : de⊙ B)
      → s (fst f a) b == d (smin a b)
    s-f a b = app= (snd (q b)) a

    s-f-b₀ : ∀ (a : de⊙ A)
      → s-f a b₀ == s-b₀ (fst f a) ∙ s₀-f a
    s-f-b₀ a =
      app= (snd (q b₀)) a
        =⟨ ↓-app=cst-out' (apd (λ u → app= (snd u) a) q-f) ⟩
      s-b₀ (fst f a) ∙' app= (snd q₀) a
        =⟨ ap (s-b₀ (fst f a) ∙'_) (app=-β s₀-f a) ⟩
      s-b₀ (fst f a) ∙' s₀-f a
        =⟨ ∙'=∙ (s-b₀ (fst f a)) (s₀-f a) ⟩
      s-b₀ (fst f a) ∙ s₀-f a =∎

    e₂ : ∀ (b : de⊙ B) →
      s a₀' b
      =-=
      transport! (fst ∘ P) (smgluer b) (transport (fst ∘ P) (smgluer b₀) (d smbaser))
    e₂ b =
      s a₀' b
        =⟪ to-transp! (apd (λ a' → s a' b) (! (snd f))) ⟫
      transport! (λ a' → fst (P (smin a' b))) (! (snd f)) (s (fst f a₀) b)
        =⟪ ap (transport! (λ a' → fst (P (smin a' b))) (! (snd f)))
              (s-f a₀ b) ⟫
      transport! (λ a' → fst (P (smin a' b))) (! (snd f)) (d (smin a₀ b))
        =⟪ ap (transport! (λ a' → fst (P (smin a' b))) (! (snd f)))
              (to-transp! (apd d (smgluer b))) ⟫
      {!transport! (λ a' → fst (P (smin a' b))) (! (snd f))
                  (transport! (λ z → fst (P (∧-fmap f (⊙idf B) z))) (smgluer b) (d smbaser))
        =⟪ ? ⟫
      ?!}

    section-smbasel : fst (P smbasel)
    section-smbasel = transport (fst ∘ P) (smgluel a₀') (d smbasel)

    section-smbaser : fst (P smbaser)
    section-smbaser = transport (fst ∘ P) (smgluer b₀) (d smbaser)

    section-smgluel' : ∀ (a' : de⊙ A') → s₀ a' == section-smbasel [ fst ∘ P ↓ smgluel a' ]
    section-smgluel' a' = foo (A' ∧ B) (fst ∘ P) (d smbasel) (smgluel a') (smgluel a₀')

    section-smgluel : ∀ (a' : de⊙ A') → s a' b₀ == section-smbasel [ fst ∘ P ↓ smgluel a' ]
    section-smgluel a' = s-b₀ a' ◃ section-smgluel' a'

    section-smgluer : ∀ (b : de⊙ B) → s a₀' b == section-smbaser [ fst ∘ P ↓ smgluer b ]
    section-smgluer b = from-transp! (fst ∘ P) (smgluer b) (↯ (e₂ b))

    module Section =
      SmashElim
        {P = fst ∘ P}
        s
        section-smbasel
        section-smbaser
        section-smgluel
        section-smgluer

    section : Π (A' ∧ B) (fst ∘ P)
    section = Section.f

    d-smbase-lr : d smbasel == d smbaser
    d-smbase-lr =
      transport
        (λ p → d smbasel == d smbaser [ fst ∘ P ↓ p ]) (↯ r)
        (↓-ap-in
          (fst ∘ P)
          (∧-fmap f (⊙idf B))
          (apd d (! (smgluel a₀) ∙ smgluer b₀)))
      where
      r : ap (∧-fmap f (⊙idf B)) (! (smgluel a₀) ∙ smgluer b₀) =-= idp
      r =
        ap (∧-fmap f (⊙idf B)) (! (smgluel a₀) ∙ smgluer b₀)
          =⟪ ap-∙ (∧-fmap f (⊙idf B)) (! (smgluel a₀)) (smgluer b₀) ⟫
        ap (∧-fmap f (⊙idf B)) (! (smgluel a₀)) ∙ ap (∧-fmap f (⊙idf B)) (smgluer b₀)
          =⟪ ap2 _∙_ (ap-! (∧-fmap f (⊙idf B)) (smgluel a₀) ∙
                      ap ! (∧-fmap-smgluel-β' f (⊙idf B) a₀))
                     (∧-fmap-smgluer-β' f (⊙idf B) b₀) ⟫
        ! (∧-norm-l (fst f a₀)) ∙
        ap (λ a' → smin a' b₀) (snd f) ∙
        ∧-norm-r b₀
          =⟪ ! (∙-assoc (! (∧-norm-l (fst f a₀)))
                        (ap (λ a' → smin a' b₀) (snd f))
                        (∧-norm-r b₀)) ⟫
        (! (∧-norm-l (fst f a₀)) ∙ ap (λ a' → smin a' b₀) (snd f)) ∙
        ∧-norm-r b₀
          =⟪ ap2 _∙_ (ap (! (∧-norm-l (fst f a₀)) ∙_) (homotopy-to-cst-ap (λ a' → smin a' b₀) smbasel smgluel (snd f)) ∙
                      !-inv-l (∧-norm-l (fst f a₀)))
                     (!-inv-r (smgluer b₀)) ⟫
        idp ∎∎

    is-section-smbasel : section (∧-fmap f (⊙idf B) smbasel) == d smbasel
    is-section-smbasel = ↯ s-a₀'-b₀

    is-section-smbaser : section (∧-fmap f (⊙idf B) smbaser) == d smbaser
    is-section-smbaser = ↯ (s-a₀'-b₀ ∙∙ d-smbase-lr ◃∎)

    is-section-smgluel : ∀ (a : de⊙ A) →
      s-f a b₀ ◃ apd d (smgluel a)
      ==
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluel a) ▹
      is-section-smbasel
    is-section-smgluel a =
      s-f a b₀ ◃ apd d (smgluel a)
        =⟨ ap (_◃ apd d (smgluel a)) (s-f-b₀ a) ⟩
      (s-b₀ (fst f a) ∙ s₀-f a) ◃ apd d (smgluel a)
        =⟨ bar
             (A' ∧ B)
             (fst ∘ P)
             (∧-fmap f (⊙idf B))
             (smgluel a)
             d
             (smgluel (fst f a))
             (smgluel a₀')
             (∧-fmap-smgluel-β-∙' a)
             (s-b₀ a₀')
             (s-b₀ (fst f a)) ⟩
      ↓-ap-out= (fst ∘ P)
                (∧-fmap f (⊙idf B))
                (smgluel a)
                (∧-fmap-smgluel-β-∙ a)
                (section-smgluel (fst f a) ∙ᵈ !ᵈ (section-smgluel a₀')) ▹
      is-section-smbasel
        =⟨ ! $ ap (_▹ is-section-smbasel) $
           ap (↓-ap-out= (fst ∘ P)
                         (∧-fmap f (⊙idf B))
                         (smgluel a)
                         (∧-fmap-smgluel-β-∙ a)) $
           apd-section-norm-l (fst f a) ⟩
      ↓-ap-out= (fst ∘ P)
                (∧-fmap f (⊙idf B))
                (smgluel a)
                (∧-fmap-smgluel-β-∙ a)
                (apd section (∧-norm-l (fst f a))) ▹
      is-section-smbasel
        =⟨ ! $ ap (_▹ is-section-smbasel) $
           apd-∘'' section
                   (∧-fmap f (⊙idf B))
                   (smgluel a)
                   (∧-fmap-smgluel-β-∙ a) ⟩
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluel a) ▹
      is-section-smbasel =∎
      where
      apd-section-norm-l : ∀ (a' : de⊙ A') →
        apd section (∧-norm-l a')
        ==
        section-smgluel a' ∙ᵈ !ᵈ (section-smgluel a₀')
      apd-section-norm-l a' =
        apd section (∧-norm-l a')
          =⟨ apd-∙ section (smgluel a') (! (smgluel a₀')) ⟩
        apd section (smgluel a') ∙ᵈ apd section (! (smgluel a₀'))
          =⟨ ap2 _∙ᵈ_ (Section.smgluel-β a')
                      (apd-! section (smgluel a₀') ∙
                       ap !ᵈ (Section.smgluel-β a₀')) ⟩
        section-smgluel a' ∙ᵈ !ᵈ (section-smgluel a₀') =∎

    is-section-smgluer : ∀ (b : de⊙ B) →
      s-f a₀ b ◃
      apd d (smgluer b)
      ==
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluer b) ▹
      is-section-smbaser
    is-section-smgluer b =
      {!!}

    is-section : section ∘ ∧-fmap f (⊙idf B) ∼ d
    is-section =
      Smash-PathOver-elim
        {P = λ ab → fst (P (∧-fmap f (⊙idf B) ab))}
        (section ∘ ∧-fmap f (⊙idf B))
        d
        s-f
        is-section-smbasel
        is-section-smbaser
        is-section-smgluel
        is-section-smgluer

  -- Proposition 4.3.2 in Guillaume Brunerie's thesis
  ∧-fmap-conn-l : has-conn-fibers (m +2+ n) (∧-fmap f (⊙idf B))
  ∧-fmap-conn-l = conn-in (λ P → ConnIn.section P , ConnIn.is-section P)
