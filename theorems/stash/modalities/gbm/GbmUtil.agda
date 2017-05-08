{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.gbm.GbmUtil where

  BM-Relation : ∀ {ℓ} (M : Modality ℓ) {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ) → Type ℓ
  BM-Relation M {A} {B} Q =
    {a₀ : A} {b₀ : B} (q₀ : Q a₀ b₀)
    {a₁ : A} (q₁ : Q a₁ b₀)
    {b₁ : B} (q₂ : Q a₀ b₁) → 
    Modality.is-◯-connected M (((a₀ , q₀) == (a₁ , q₁)) * ((b₀ , q₀) == (b₁ , q₂)))


  prop-lemma : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
               (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
               x₀ == x₁ [ (fst ∘ P) ↓ p ]
  prop-lemma P idp x₀ x₁ = prop-has-all-paths (snd (P _)) x₀ x₁              

  pths-ovr-is-prop : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
                     (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
                     is-prop (x₀ == x₁ [ (fst ∘ P) ↓ p ])
  pths-ovr-is-prop P idp x₀ x₁ = =-preserves-level (snd (P _))                             

  pths-ovr-contr : ∀ {ℓ} {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
                     (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
                     is-contr (x₀ == x₁ [ (fst ∘ P) ↓ p ])
  pths-ovr-contr P idp x₀ x₁ = =-preserves-level (inhab-prop-is-contr x₀ (snd (P _)))
  
  eqv-square : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B)
    {b b' : B} (p : b == b')
    → ap (–> e ∘ <– e) p == (<–-inv-r e b) ∙ p ∙ (! (<–-inv-r e b'))
  eqv-square e idp = ! (!-inv-r (<–-inv-r e _))

  eqv-square' : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B)
    {a a' : A} (p : a == a')
    → ap (<– e ∘ –> e) p == <–-inv-l e a ∙ p ∙ ! (<–-inv-l e a')
  eqv-square' e idp = ! (!-inv-r (<–-inv-l e _))
                
  ↓-==-in : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
    {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u ∙ ap g p) == (ap f p ∙ v)
    → (u == v [ (λ x → f x == g x) ↓ p ])
  ↓-==-in {p = idp} q = ! (∙-unit-r _) ∙ q

  ↓-==-out : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
    {x y : A} {p : x == y} {u : f x == g x} {v : f y == g y}
    → (u == v [ (λ x → f x == g x) ↓ p ])
    → (u ∙ ap g p) == (ap f p ∙ v)
  ↓-==-out {p = idp} q = (∙-unit-r _) ∙ q 

  module HFiberSrcEquiv {i₀ i₁ i₂} {A : Type i₀} {B : Type i₁} {C : Type i₂}
    (f : A → B) (h : B → C) (k : A → C)
    (w : (a : A) → h (f a) == k a)
    (ise-f : is-equiv f) 
    where

     private
       g = is-equiv.g ise-f
       f-g = is-equiv.f-g ise-f
       g-f = is-equiv.g-f ise-f
       adj = is-equiv.adj ise-f
       adj' = is-equiv.adj' ise-f

       to : (c : C) → hfiber k c → hfiber h c
       to .(k a) (a , idp) = f a , w a

       to-lem₀ : (c : C) (x : hfiber k c) → fst (to c x) == f (fst x)
       to-lem₀ .(k a) (a , idp) = idp

       to-lem₁ : (c : C) (x : hfiber k c) → snd (to c x) == ap h (to-lem₀ c x) ∙ w (fst x) ∙ snd x 
       to-lem₁ .(k a) (a , idp) = ! (∙-unit-r (w a))
    
       from : (c : C) → hfiber h c → hfiber k c
       from .(h b) (b , idp) = g b , ! (w (g b)) ∙ ap h (f-g b)

       from-lem₀ : (c : C) (x : hfiber h c) → fst (from c x) == g (fst x)
       from-lem₀ .(h b) (b , idp) = idp

       from-lem₁ : (c : C) (x : hfiber h c) → snd (from c x) == ap k (from-lem₀ c x) ∙ (! (w (g (fst x)))) ∙ ap h (f-g (fst x)) ∙ snd x
       from-lem₁ .(h b) (b , idp) = ap (λ p → ! (w (g b)) ∙ p) (! (∙-unit-r (ap h (f-g b))))

       to-from : (c : C) (x : hfiber h c) → to c (from c x) == x
       to-from .(h b) (b , idp) = pair= (q ∙ f-g b) (↓-app=cst-in (r ∙ eq))

         where c = h b
               p = ! (w (g b)) ∙ ap h (f-g b)
               q = to-lem₀ c (g b , p)
               r = to-lem₁ c (g b , p)

               eq = ap h q ∙ w (g b) ∙ ! (w (g b)) ∙ ap h (f-g b)
                      =⟨ ! (∙-assoc (w (g b)) (! (w (g b))) (ap h (f-g b))) |in-ctx (λ x → ap h q ∙ x) ⟩
                    ap h q ∙ (w (g b) ∙ (! (w (g b)))) ∙ ap h (f-g b)
                      =⟨ !-inv-r (w (g b)) |in-ctx (λ x → ap h q ∙ x ∙ ap h (f-g b)) ⟩ 
                    ap h q ∙ ap h (f-g b)
                      =⟨ ∙-ap h q (f-g b) ⟩
                    ap h (q ∙ f-g b)
                      =⟨ ! (∙-unit-r (ap h (q ∙ f-g b))) ⟩ 
                    ap h (q ∙ f-g b) ∙ idp ∎

       from-to : (c : C) (x : hfiber k c) → from c (to c x) == x
       from-to .(k a) (a , idp) = pair= (p ∙ g-f a) (↓-app=cst-in (q ∙ eq))

         where c = k a
               p = from-lem₀ c (f a , w a)
               q = from-lem₁ c (f a , w a)

               eq = ap k p ∙ ! (w (g (f a))) ∙ ap h (f-g (f a)) ∙ w a
                       =⟨ ! (adj a) |in-ctx (λ x → ap k p ∙ ! (w (g (f a))) ∙ ap h x ∙ w a) ⟩
                    ap k p ∙ ! (w (g (f a))) ∙ ap h (ap f (g-f a)) ∙ w a
                       =⟨ ∘-ap h f (g-f a) |in-ctx (λ x → ap k p ∙ ! (w (g (f a))) ∙ x ∙ w a) ⟩ 
                    ap k p ∙ ! (w (g (f a))) ∙ ap (h ∘ f) (g-f a) ∙ w a
                       =⟨ ! (↓-='-out (apd w (g-f a))) |in-ctx (λ x → ap k p ∙ ! (w (g (f a))) ∙ x) ⟩
                    ap k p ∙ ! (w (g (f a))) ∙ w (g (f a)) ∙' ap k (g-f a)
                       =⟨ ∙'=∙ (w (g (f a))) (ap k (g-f a)) |in-ctx (λ x → ap k p ∙ ! (w (g (f a))) ∙ x) ⟩ 
                    ap k p ∙ ! (w (g (f a))) ∙ w (g (f a)) ∙ ap k (g-f a)
                       =⟨ ! (∙-assoc (! (w (g (f a)))) (w (g (f a))) (ap k (g-f a))) |in-ctx (λ x → ap k p ∙ x) ⟩ 
                    ap k p ∙ (! (w (g (f a))) ∙ w (g (f a))) ∙ ap k (g-f a)
                       =⟨ !-inv-l (w (g (f a))) |in-ctx (λ x → ap k p ∙ x ∙ ap k (g-f a)) ⟩ 
                    ap k p ∙ ap k (g-f a)
                       =⟨ ∙-ap k p (g-f a) ⟩ 
                    ap k (p ∙ g-f a)
                      =⟨ ! (∙-unit-r (ap k (p ∙ g-f a))) ⟩ 
                    ap k (p ∙ g-f a) ∙ idp ∎

     eqv : (c : C) → hfiber k c ≃ hfiber h c
     eqv c = equiv (to c) (from c) (to-from c) (from-to c)


  module HFiberTgtEquiv {i₀ i₁ i₂} {A : Type i₀} {B : Type i₁} {C : Type i₂}
    (h : A → B) (k : A → C) (f : B → C)
    (w : (a : A) → k a == f (h a))
    (ise-f : is-equiv f) 
    where

     private
       g = is-equiv.g ise-f
       f-g = is-equiv.f-g ise-f
       g-f = is-equiv.g-f ise-f
       adj = is-equiv.adj ise-f
       adj' = is-equiv.adj' ise-f

       to : (b : B) → hfiber h b → hfiber k (f b)
       to .(h a) (a , idp) = a , w a

       to-lem₀ : (b : B) (x : hfiber h b) → fst (to b x) == fst x
       to-lem₀ .(h a) (a , idp) = idp

       to-lem₁ : (b : B) (x : hfiber h b) → snd (to b x) == ap k (to-lem₀ b x) ∙ w (fst x) ∙ ap f (snd x)
       to-lem₁ .(h a) (a , idp) = ! (∙-unit-r (w a))
       
       from : (b : B) → hfiber k (f b) → hfiber h b
       from b (a , p) = a , (! (g-f (h a)) ∙ ap g (! (w a) ∙ p) ∙ g-f b)

       to-from : (b : B) (x : hfiber k (f b)) → to b (from b x) == x
       to-from b (a , p) = pair= r (↓-app=cst-in (s ∙ (ap (λ x → ap k r ∙ x) eq)))

         where q = ! (g-f (h a)) ∙ ap g (! (w a) ∙ p) ∙ g-f b
               r = to-lem₀ b (a , q)
               s = to-lem₁ b (a , q)

               eq = w a ∙ ap f q
                      =⟨ ! (∙-ap f (! (g-f (h a))) (ap g (! (w a) ∙ p) ∙ g-f b)) |in-ctx (λ x → w a ∙ x) ⟩
                    w a ∙ ap f (! (g-f (h a))) ∙ ap f (ap g (! (w a) ∙ p) ∙ g-f b)
                      =⟨ ! (∙-ap f (ap g (! (w a) ∙ p)) (g-f b)) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ x) ⟩
                    w a ∙ ap f (! (g-f (h a))) ∙ ap f (ap g (! (w a) ∙ p)) ∙ ap f (g-f b)
                      =⟨ ∘-ap f g (! (w a) ∙ p) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ x ∙ ap f (g-f b)) ⟩
                    w a ∙ ap f (! (g-f (h a))) ∙ ap (f ∘ g) (! (w a) ∙ p) ∙ ap f (g-f b)
                      =⟨ ap (λ x → w a ∙ ap f (! (g-f (h a))) ∙ x ∙ ap f (g-f b)) (eqv-square (f , ise-f) (! (w a) ∙ p)) ⟩
                    w a ∙ ap f (! (g-f (h a))) ∙ (f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ ! (f-g (f b))) ∙ ap f (g-f b)
                      =⟨ adj b |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ (f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ ! (f-g (f b))) ∙ x) ⟩ 
                    w a ∙ ap f (! (g-f (h a))) ∙ (f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ ! (f-g (f b))) ∙ f-g (f b)
                      =⟨ ∙-assoc (f-g (f (h a))) ((! (w a) ∙ p) ∙ ! (f-g (f b))) (f-g (f b)) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ x) ⟩
                    w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ ((! (w a) ∙ p) ∙ ! (f-g (f b))) ∙ f-g (f b)
                      =⟨ ∙-assoc (! (w a) ∙ p) (! (f-g (f b))) (f-g (f b)) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ x) ⟩ 
                    w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ ! (f-g (f b)) ∙ f-g (f b)
                      =⟨ !-inv-l (f-g (f b)) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ x) ⟩ 
                    w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ (! (w a) ∙ p) ∙ idp
                      =⟨ ∙-unit-r (! (w a) ∙ p) |in-ctx (λ x → w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ x) ⟩ 
                    w a ∙ ap f (! (g-f (h a))) ∙ f-g (f (h a)) ∙ ! (w a) ∙ p
                      =⟨ ap-! f (g-f (h a)) |in-ctx (λ x → w a ∙ x ∙ f-g (f (h a)) ∙ ! (w a) ∙ p) ⟩
                    w a ∙ ! (ap f (g-f (h a))) ∙ f-g (f (h a)) ∙ ! (w a) ∙ p
                      =⟨ ! (adj (h a)) |in-ctx (λ x → w a ∙ ! (ap f (g-f (h a))) ∙ x ∙ ! (w a) ∙ p) ⟩ 
                    w a ∙ ! (ap f (g-f (h a))) ∙ ap f (g-f (h a)) ∙ ! (w a) ∙ p
                      =⟨ ! (∙-assoc (! (ap f (g-f (h a)))) (ap f (g-f (h a))) (! (w a) ∙ p)) |in-ctx (λ x → w a ∙ x)⟩
                    w a ∙ (! (ap f (g-f (h a))) ∙ ap f (g-f (h a))) ∙ ! (w a) ∙ p
                      =⟨ !-inv-l (ap f (g-f (h a))) |in-ctx (λ x → w a ∙ x ∙ ! (w a) ∙ p)⟩ 
                    w a ∙ ! (w a) ∙ p
                      =⟨ ! (∙-assoc (w a) (! (w a)) p) ⟩
                    (w a ∙ ! (w a)) ∙ p
                      =⟨ !-inv-r (w a) |in-ctx (λ x → x ∙ p) ⟩ 
                    p ∎

       from-to : (b : B) (x : hfiber h b) → from b (to b x) == x
       from-to .(h a) (a , idp) = pair= idp eq

         where eq = ! (g-f (h a)) ∙ ap g (! (w a) ∙ w a) ∙ g-f (h a)
                      =⟨ !-inv-l (w a)|in-ctx (λ x → ! (g-f (h a)) ∙ ap g x ∙ g-f (h a)) ⟩
                    ! (g-f (h a)) ∙ g-f (h a)
                      =⟨ !-inv-l (g-f (h a)) ⟩ 
                    idp ∎
       
     eqv : (b : B) → hfiber h b ≃ hfiber k (f b)
     eqv b = equiv (to b) (from b) (to-from b) (from-to b)

  module HFiberSqEquiv {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
    (sq : CommSquare f₀ f₁ hA hB) (ise-hA : is-equiv hA) (ise-hB : is-equiv hB) where

    open CommSquare

    private
      gB = is-equiv.g ise-hB

    
    module Src = HFiberSrcEquiv hA f₁ (hB ∘ f₀) (λ a₀ → ! (commutes sq a₀)) ise-hA
    module Tgt = HFiberTgtEquiv f₀ (f₁ ∘ hA) hB (λ a₀ → ! (commutes sq a₀)) ise-hB

    eqv : (b₀ : B₀) → hfiber f₀ b₀ ≃ hfiber f₁ (hB b₀)
    eqv b₀ = Src.eqv (hB b₀)
      ∘e coe-equiv (ap (λ s → hfiber s (hB b₀)) (λ= (λ a₀ → ! (commutes sq a₀))))
      ∘e Tgt.eqv b₀

  hfiber-sq-eqv : ∀ {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
    (sq : CommSquare f₀ f₁ hA hB) (ise-hA : is-equiv hA) (ise-hB : is-equiv hB) →
    (b₀ : B₀) → hfiber f₀ b₀ ≃ hfiber f₁ (hB b₀)
  hfiber-sq-eqv f₀ f₁ hA hB sq ise-hA ise-hB b₀ = M.eqv b₀

    where module M = HFiberSqEquiv f₀ f₁ hA hB sq ise-hA ise-hB
