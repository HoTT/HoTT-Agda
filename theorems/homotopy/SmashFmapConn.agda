{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.SmashFmapConn where

module _ {i} {j} {A : Type i} (B : A → Type j) where

  custom-assoc : {a₀ a₁ a₂ a₃ : A}
    {b₀ : B a₀} {b₁ b₁' b₁'' : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    {p : a₀ == a₁} (p' : b₀ == b₁ [ B ↓ p ])
    (q' : b₁ == b₁')
    (r' : b₁' == b₁'')
    {s : a₁ == a₂} (s' : b₁'' == b₂ [ B ↓ s ])
    {t : a₂ == a₃} (t' : b₂ == b₃ [ B ↓ t ])
    → p' ∙ᵈ (((q' ∙ r') ◃ s') ∙ᵈ t')
      ==
      ((p' ▹ q') ▹ r') ∙ᵈ s' ∙ᵈ t'
  custom-assoc {p = idp} p'@idp q'@idp r'@idp {s = idp} s'@idp {t = idp} t' = idp

  transp-over : {a₀ a₁ : A} (p : a₀ == a₁) (b₀ : B a₀)
    → b₀ == transport B p b₀ [ B ↓ p ]
  transp-over p b₀ = from-transp B p (idp {a = transport B p b₀})

  transp-over-naturality : ∀ {a₀ a₁ : A} (p : a₀ == a₁)
    {b₀ b₀' : B a₀} (q : b₀ == b₀')
    → q ◃ transp-over p b₀'
      ==
      transp-over p b₀ ▹ ap (transport B p) q
  transp-over-naturality p@idp q@idp = idp

  to-transp-over : {a₀ a₁ : A} {p : a₀ == a₁}
    {b₀ : B a₀} {b₁ : B a₁} (q : b₀ == b₁ [ B ↓ p ])
    → q ▹ ! (to-transp q) == transp-over p b₀
  to-transp-over {p = idp} q@idp = idp

module _ {i} {j} {S* : Type i} (P* : S* → Type j) where

  -- cpa = custom path algebra
  cpa₁ : {s₁ s₂ t : S*} (p* : P* s₂) (p₁ : s₁ == t) (p₂ : s₂ == t)
    → transport P* (! (p₁ ∙ ! p₂)) p*  == transport P* p₂ p* [ P* ↓ p₁ ]
  cpa₁ p* p₁@idp p₂@idp = idp

  -- cpac = custom path algebra coherence
  cpac₁ : ∀ {k} {C : Type k} (f : C → S*)
    {c₁ c₂ : C} (q : c₁ == c₂)
    (d : Π C (P* ∘ f))
    {t : S*} (p₁ : f c₁ == t) (p₂ : f c₂ == t)
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
                ((v' ◃ cpa₁ (d c₂) p₁ p₂) ∙ᵈ !ᵈ (v ◃ cpa₁ (d c₂) p₂ p₂)) ▹
      (v ∙ ap (λ pp → transport P* (! pp) (d c₂)) (!-inv-r p₂))
  cpac₁ f q@idp d p₁@.idp p₂@idp r@idp v@idp v'@idp = idp

  cpa₂ : ∀ {k} {C : Type k} (f : C → S*)
    {c₁ c₂ : C} (q : c₁ == c₂)
    (d : Π C (P* ∘ f))
    {s t : S*} (p : f c₁ == s) (r : s == t) (u : f c₂ == t)
    (h : ap f q == p ∙' (r ∙ ! u))
    → transport P* p (d c₁)
      ==
      transport P* u (d c₂)
        [ P* ↓ r ]
  cpa₂ f q@idp d p@.idp r@idp u@idp h@idp = idp

  cpac₂ : ∀ {k} {C : Type k} (f : C → S*)
    {c₁ c₂ c₃ : C} (q : c₁ == c₂) (q' : c₃ == c₂)
    (d : Π C (P* ∘ f))
    {s t : S*} (p : f c₁ == s) (p' : f c₃ == f c₂) (r : s == t) (u : f c₂ == t)
    (h : ap f q == p ∙' (r ∙ ! u))
    (h' : ap f q' == p' ∙' u ∙ ! u)
    {x : P* (f c₂)} (x' : x == transport P* p' (d c₃))
    {y : P* (f c₁)} (y' : y == d c₁)
    → ↓-ap-out=
        P*
        f
        q
        (h ∙ ∙'=∙ p (r ∙ ! u))
        ((y' ◃ transp-over P* p (d c₁)) ∙ᵈ cpa₂ f q d p r u h ∙ᵈ !ᵈ (x' ◃ cpa₂ f q' d p' u u h')) ▹
      (x' ∙
       ap (λ pp → transport P* pp (d c₃))
          (! (∙-unit-r p') ∙
           ap (p' ∙_) (! (!-inv-r u)) ∙
           ! (h' ∙ ∙'=∙ p' (u ∙ ! u))) ∙
       to-transp (↓-ap-in P* f (apd d q')))
      ==
      y' ◃ apd d q
  cpac₂ f q@idp q'@idp d p@.idp p'@.idp r@idp u@idp h@idp h'@idp x'@idp y'@idp = idp

module _ {i} {j} {k} {A : Ptd i} {A' : Ptd j} (f : A ⊙→ A') (B : Ptd k)
         {m n : ℕ₋₂}
         (f-is-m-conn : has-conn-fibers m (fst f))
         (B-is-Sn-conn : is-connected (S n) (de⊙ B)) where

  private
    a₀ = pt A
    a₀' = pt A'
    b₀ = pt B

  module ConnIn (P : A' ∧ B → (n +2+ m) -Type (lmax i (lmax j k)))
                (d : ∀ (ab : A ∧ B) → fst (P (∧-fmap f (⊙idf B) ab))) where

    h : ∀ (b : de⊙ B)
      → (∀ (a' : de⊙ A') → fst (P (smin a' b)))
      → (∀ (a : de⊙ A) → fst (P (smin (fst f a) b)))
    h b s = s ∘ fst f

    Q : de⊙ B → n -Type (lmax i (lmax j k))
    Q b = Q' , Q'-level
      where
      Q' : Type (lmax i (lmax j k))
      Q' = hfiber (h b) (λ a → d (smin a b))
      Q'-level : has-level n Q'
      Q'-level =
        conn-extend-general
          {n = m} {k = n}
          f-is-m-conn
          (λ a → P (smin a b))
          (λ a → d (smin a b))

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

    ∧-fmap-smgluer-β-∙' : ∀ (b : de⊙ B) →
      ap (∧-fmap f (⊙idf B)) (smgluer b)
      ==
      ap (λ a' → smin a' b) (snd f) ∙' ∧-norm-r b
    ∧-fmap-smgluer-β-∙' b =
      ∧-fmap-smgluer-β' f (⊙idf B) b ∙
      ∙=∙' (ap (λ a' → smin a' b) (snd f)) (∧-norm-r b)

    ∧-fmap-smgluer-β-∙ : ∀ (b : de⊙ B) →
      ap (∧-fmap f (⊙idf B)) (smgluer b)
      ==
      ap (λ a' → smin a' b) (snd f) ∙ ∧-norm-r b
    ∧-fmap-smgluer-β-∙ b =
      ∧-fmap-smgluer-β-∙' b ∙
      ∙'=∙ (ap (λ a' → smin a' b) (snd f)) (∧-norm-r b)

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

    s-a₀' : ∀ (b : de⊙ B) →
      s a₀' b
      ==
      transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b))
    s-a₀' b = ↯ $
      s a₀' b
        =⟪ ! (to-transp (↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)))) ⟫
      transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (s (fst f a₀) b)
        =⟪ ap (transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f)))
              (s-f a₀ b) ⟫
      transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b)) ∎∎

    section-smbasel : fst (P smbasel)
    section-smbasel = transport (fst ∘ P) (smgluel a₀') (d smbasel)

    section-smbaser : fst (P smbaser)
    section-smbaser = transport (fst ∘ P) (smgluer b₀) (d smbaser)

    section-smgluel' : ∀ (a' : de⊙ A') → s₀ a' == section-smbasel [ fst ∘ P ↓ smgluel a' ]
    section-smgluel' a' = cpa₁ (fst ∘ P) (d smbasel) (smgluel a') (smgluel a₀')

    section-smgluel : ∀ (a' : de⊙ A') → s a' b₀ == section-smbasel [ fst ∘ P ↓ smgluel a' ]
    section-smgluel a' = s-b₀ a' ◃ section-smgluel' a'

    section-smgluer' : ∀ (b : de⊙ B) →
      transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b))
      ==
      section-smbaser
      [ fst ∘ P ↓ smgluer b ]
    section-smgluer' b =
      cpa₂
        (fst ∘ P)
        (∧-fmap f (⊙idf B))
        (smgluer b)
        d
        (ap (λ a' → smin a' b) (snd f))
        (smgluer b)
        (smgluer b₀)
        (∧-fmap-smgluer-β-∙' b)

    section-smgluer : ∀ (b : de⊙ B) → s a₀' b == section-smbaser [ fst ∘ P ↓ smgluer b ]
    section-smgluer b = s-a₀' b ◃ section-smgluer' b

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

    is-section-smbasel : s a₀' b₀ == d smbasel
    is-section-smbasel = ↯ $
      s a₀' b₀
        =⟪ s-b₀ a₀' ⟫
      s₀ a₀'
        =⟪idp⟫
      transport (fst ∘ P) (! (∧-norm-l a₀')) (d smbasel)
        =⟪ ap (λ p → transport (fst ∘ P) (! p) (d smbasel))
              (!-inv-r (smgluel a₀')) ⟫
      d smbasel ∎∎

    is-section-smgluel : ∀ (a : de⊙ A) →
      s-f a b₀ ◃ apd d (smgluel a)
      ==
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluel a) ▹
      is-section-smbasel
    is-section-smgluel a =
      s-f a b₀ ◃ apd d (smgluel a)
        =⟨ ap (_◃ apd d (smgluel a)) (s-f-b₀ a) ⟩
      (s-b₀ (fst f a) ∙ s₀-f a) ◃ apd d (smgluel a)
        =⟨ cpac₁
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

    is-section-smbaser : s a₀' b₀ == d smbaser
    is-section-smbaser = ↯ $
      s a₀' b₀
        =⟪ s-a₀' b₀ ⟫
      transport (fst ∘ P) (ap (λ a' → smin a' b₀) (snd f)) (d (smin a₀ b₀))
        =⟪ ap (λ p → transport (fst ∘ P) p (d (smin a₀ b₀))) (↯ r) ⟫
      transport (fst ∘ P) (ap (∧-fmap f (⊙idf B)) (smgluer b₀)) (d (smin a₀ b₀))
        =⟪ to-transp (↓-ap-in (fst ∘ P) (∧-fmap f (⊙idf B)) (apd d (smgluer b₀))) ⟫
      d smbaser ∎∎
      where
      r : ap (λ a' → smin a' b₀) (snd f) =-= ap (∧-fmap f (⊙idf B)) (smgluer b₀)
      r =
        ap (λ a' → smin a' b₀) (snd f)
          =⟪ ! (∙-unit-r _) ⟫
        ap (λ a' → smin a' b₀) (snd f) ∙ idp
          =⟪ ap (ap (λ a' → smin a' b₀) (snd f) ∙_)
                (! (!-inv-r (smgluer b₀))) ⟫
        ap (λ a' → smin a' b₀) (snd f) ∙ ∧-norm-r b₀
          =⟪ ! (∧-fmap-smgluer-β-∙ b₀) ⟫
        ap (∧-fmap f (⊙idf B)) (smgluer b₀) ∎∎

    is-section-smgluer : ∀ (b : de⊙ B) →
      s-f a₀ b ◃
      apd d (smgluer b)
      ==
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluer b) ▹
      is-section-smbaser
    is-section-smgluer b = ! $
      apd (section ∘ ∧-fmap f (⊙idf B)) (smgluer b) ▹
      is-section-smbaser
        =⟨ ap (_▹ is-section-smbaser) $
           apd-∘'' section
                  (∧-fmap f (⊙idf B))
                  (smgluer b)
                  (∧-fmap-smgluer-β-∙ b) ⟩
      ↓-ap-out= (fst ∘ P)
                (∧-fmap f (⊙idf B))
                (smgluer b)
                (∧-fmap-smgluer-β-∙ b)
                (apd section (ap (λ a' → smin a' b) (snd f) ∙ ∧-norm-r b)) ▹
      is-section-smbaser
        =⟨ ap (_▹ is-section-smbaser) $
           ap (↓-ap-out= (fst ∘ P)
                         (∧-fmap f (⊙idf B))
                         (smgluer b)
                         (∧-fmap-smgluer-β-∙ b)) $
           apd-section-helper ⟩
      ↓-ap-out= (fst ∘ P)
                (∧-fmap f (⊙idf B))
                (smgluer b)
                (∧-fmap-smgluer-β-∙ b)
                ((s-f a₀ b ◃ transp-over (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b))) ∙ᵈ
                 section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)) ▹
      is-section-smbaser
        =⟨ cpac₂
             (fst ∘ P)
             (∧-fmap f (⊙idf B))
             (smgluer b)
             (smgluer b₀)
             d
             (ap (λ a' → smin a' b) (snd f))
             (ap (λ a' → smin a' b₀) (snd f))
             (smgluer b)
             (smgluer b₀)
             (∧-fmap-smgluer-β-∙' b)
             (∧-fmap-smgluer-β-∙' b₀)
             (s-a₀' b₀)
             (s-f a₀ b) ⟩
      s-f a₀ b ◃
      apd d (smgluer b) =∎
      where
      apd-section-helper :
        apd section (ap (λ a' → smin a' b) (snd f) ∙ ∧-norm-r b)
        ==
        (s-f a₀ b ◃ transp-over (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b))) ∙ᵈ
        section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)
      apd-section-helper =
        apd section (ap (λ a' → smin a' b) (snd f) ∙ ∧-norm-r b)
          =⟨ apd-∙ section (ap (λ a' → smin a' b) (snd f)) (∧-norm-r b) ⟩
        apd section (ap (λ a' → smin a' b) (snd f)) ∙ᵈ
        apd section (∧-norm-r b)
          =⟨ ap2 _∙ᵈ_
                 (apd-∘''' section (λ a' → smin a' b) (snd f))
                 (apd-∙ section (smgluer b) (! (smgluer b₀))) ⟩
        ↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)) ∙ᵈ
        apd section (smgluer b) ∙ᵈ apd section (! (smgluer b₀))
          =⟨ ap (↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)) ∙ᵈ_) $
             ap2 _∙ᵈ_
                  (Section.smgluer-β b)
                  (apd-! section (smgluer b₀) ∙
                  ap !ᵈ (Section.smgluer-β b₀)) ⟩
        ↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)) ∙ᵈ
        section-smgluer b ∙ᵈ !ᵈ (section-smgluer b₀)
          =⟨ custom-assoc (fst ∘ P)
               (↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)))
               (! (to-transp (↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)))))
               (ap (transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f))) (s-f a₀ b))
               (section-smgluer' b)
               (!ᵈ (section-smgluer b₀)) ⟩
        ((↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)) ▹
        ! (to-transp (↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f))))) ▹
        ap (transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f))) (s-f a₀ b)) ∙ᵈ
        section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)
          =⟨ ap (λ u → (u ▹ ap (transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f))) (s-f a₀ b)) ∙ᵈ
                       section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)) $
             to-transp-over (fst ∘ P) $
             ↓-ap-in (fst ∘ P) (λ a' → smin a' b) (apd (λ a' → s a' b) (snd f)) ⟩
        (transp-over (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (s (fst f a₀) b) ▹
        ap (transport (fst ∘ P) (ap (λ a' → smin a' b) (snd f))) (s-f a₀ b)) ∙ᵈ
        section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)
          =⟨ ! $ ap (_∙ᵈ section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀)) $
             transp-over-naturality (fst ∘ P)
               (ap (λ a' → smin a' b) (snd f))
               (s-f a₀ b) ⟩
        (s-f a₀ b ◃ transp-over (fst ∘ P) (ap (λ a' → smin a' b) (snd f)) (d (smin a₀ b))) ∙ᵈ
        section-smgluer' b ∙ᵈ !ᵈ (section-smgluer b₀) =∎

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
  ∧-fmap-conn-l : has-conn-fibers (n +2+ m) (∧-fmap f (⊙idf B))
  ∧-fmap-conn-l = conn-in (λ P → ConnIn.section P , ConnIn.is-section P)

private
  ∧-swap-conn : ∀ {i} {j} (X : Ptd i) (Y : Ptd j) (n : ℕ₋₂)
    → has-conn-fibers n (∧-swap X Y)
  ∧-swap-conn X Y n yx =
    Trunc-preserves-level {n = -2} n $
    equiv-is-contr-map (∧-swap-is-equiv X Y) yx

∧-fmap-conn-r : ∀ {i} {j} {k}
  (A : Ptd i) {B : Ptd j} {B' : Ptd k} (g : B ⊙→ B')
  {k l : ℕ₋₂}
  → is-connected (S k) (de⊙ A)
  → has-conn-fibers l (fst g)
  → has-conn-fibers (k +2+ l) (∧-fmap (⊙idf A) g)
∧-fmap-conn-r A {B} {B'} g {k} {l} A-is-Sk-conn g-is-l-conn =
  transport
    (has-conn-fibers (k +2+ l))
    (λ= (∧-swap-fmap (⊙idf A) g)) $
  ∘-conn (∧-swap A B)
         (∧-swap B' A ∘ ∧-fmap g (⊙idf A))
         (∧-swap-conn A B _) $
  ∘-conn (∧-fmap g (⊙idf A))
         (∧-swap B' A)
         (∧-fmap-conn-l g A g-is-l-conn A-is-Sk-conn)
         (∧-swap-conn B' A _)
