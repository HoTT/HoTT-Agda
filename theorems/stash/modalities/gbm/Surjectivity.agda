{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
import stash.modalities.gbm.Pushout

module stash.modalities.gbm.Surjectivity {ℓ} (M : Modality ℓ) where

  open Modality M
  
  Relation : Type ℓ → Type ℓ → Type (lsucc ℓ)
  Relation A B = A → B → Type ℓ

  BM-Relation : {A : Type ℓ} {B : Type ℓ} (R : Relation A B) → Type ℓ
  BM-Relation {A} {B} Q =
    {a₀ : A} {b₀ : B} (q₀ : Q a₀ b₀)
    {a₁ : A} (q₁ : Q a₁ b₀)
    {b₁ : B} (q₂ : Q a₀ b₁) → 
    is-◯-connected (((a₀ , q₀) == (a₁ , q₁)) * ((b₀ , q₀) == (b₁ , q₂)))

  prop-lemma : {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
               (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
               x₀ == x₁ [ (fst ∘ P) ↓ p ]
  prop-lemma P idp x₀ x₁ = prop-has-all-paths (snd (P _)) x₀ x₁              

  pths-ovr-is-prop : {A : Type ℓ} {a₀ a₁ : A} (P : A → hProp ℓ)
                     (p : a₀ == a₁) (x₀ : (fst ∘ P) a₀) (x₁ : (fst ∘ P) a₁) →
                     is-prop (x₀ == x₁ [ (fst ∘ P) ↓ p ])
  pths-ovr-is-prop P idp x₀ x₁ = =-preserves-level (snd (P _))                             
  
  module _ {A : Type ℓ} {B : Type ℓ} (Q : Relation A B) where

    --
    --  Right, so to finish the theorem, you need to show two things:
    --
    --  1) The implication below, so that you can apply the theorem
    --     with the new hypothesis on the restricted fibration
    --
    --  2) That the space a' == b' ≃ a == b
    --

    private

      A' : Type ℓ
      A' = Σ A (λ a → Trunc (S ⟨-2⟩) (Σ B (λ b → Q a b)))

    RestrictionOf : Relation A' B
    RestrictionOf (a , _) b = Q a b

    private
      Q' = RestrictionOf
      
    claim₀ : (a₀ a₁ : A') → (a₀ == a₁) ≃ (fst a₀ == fst a₁)
    claim₀ a₀ a₁ = equiv f g f-g g-f

      where f : a₀ == a₁ → fst a₀ == fst a₁
            f = fst=

            P : A → hProp ℓ
            P a = Trunc (S ⟨-2⟩) (Σ B (λ b → Q a b)) , Trunc-level
            
            q : (p : fst a₀ == fst a₁) → snd a₀ == snd a₁ [ _ ↓ p ]
            q p = prop-lemma P p (snd a₀) (snd a₁)
            
            g : fst a₀ == fst a₁ → a₀ == a₁
            g p = pair= p (q p)

            f-g : (p : fst a₀ == fst a₁) → f (g p) == p
            f-g p = fst=-β p (q p)

            g-f : (p : a₀ == a₁) → g (f p) == p
            g-f p = ap (λ x → pair= (fst= p) x) pp ∙ (! (pair=-η p))

              where pp : q (fst= p) == snd= p
                    pp = fst (pths-ovr-is-prop P (fst= p) (snd a₀) (snd a₁) (q (fst= p)) (snd= p))

    next-claim : {a₀ a₁ : A'} {b : B} (q₀ : Q' a₀ b) (q₁ : Q' a₁ b) (p : a₀ == a₁)
                 → (q₀ == q₁ [ (λ a → Q' a b) ↓ p ]) ≃ (q₀ == q₁ [ (λ a → Q a b) ↓ fst= p ])
    next-claim q₀ q₁ idp = ide (q₀ == q₁)                 

    thm : BM-Relation Q → BM-Relation Q'
    thm H {a₀} {b₀} q₀ {a₁} q₁ {b₁} q₂ = is-◯-conn-emap claim₂ (H {fst a₀} {b₀} q₀ {fst a₁} q₁ {b₁} q₂)

      where claim₁ : (a₀ , q₀ == a₁ , q₁) ≃ (fst a₀ , q₀ == fst a₁ , q₁)
            claim₁ = (=Σ-econv (fst a₀ , q₀) (fst a₁ , q₁))
              ∘e (Σ-emap-l (λ p → q₀ == q₁ [ (λ a → Q a b₀) ↓ p ]) (claim₀ a₀ a₁))
              ∘e Σ-emap-r (next-claim q₀ q₁) 
              ∘e (=Σ-econv (a₀ , q₀) (a₁ , q₁)) ⁻¹

            claim₂ : ((fst a₀ , q₀ == fst a₁ , q₁) * (b₀ , q₀ == b₁ , q₂)) ≃
                     ((a₀ , q₀ == a₁ , q₁) * (b₀ , q₀ == b₁ , q₂))
            claim₂ = *-emap (claim₁ ⁻¹) (ide _)                            

    open import stash.modalities.gbm.PushoutMono
    open import stash.modalities.gbm.PullbackSplit
    open import homotopy.PushoutSplit

    -- Okay, now on to the pushout thing
    import stash.modalities.gbm.Pushout Q as W
    import stash.modalities.gbm.Pushout Q' as W'

    private
      Z = (Σ A λ a → Σ B λ b → Q a b)
      D = (Σ A' λ a → Σ B λ b → Q (fst a) b)

    long-span' : Span
    long-span' = span A B Z fst (fst ∘ snd)
    
    long-span : Span {ℓ} {ℓ} {ℓ}
    long-span = span A B D (fst ∘ fst) (fst ∘ snd) 

    long-span-eqv : SpanEquiv long-span long-span'
    long-span-eqv = (span-map (idf A) (idf B) (–> D-equiv-Z) {!!} {!!}) , {!!}

      where D-equiv-Z : D ≃ Z
            D-equiv-Z = equiv to from to-from from-to

              where to : D → Z
                    to ((a , e) , b , q) = a , b , q

                    from : Z → D
                    from (a , b , q) = (a , [ (b , q) ]) , (b , q)

                    to-from : (z : Z) → to (from z) == z
                    to-from (a , b , q) = idp

                    from-to : (d : D) → from (to d) == d
                    from-to ((a , e) , b , q) = pair= (pair= idp (prop-has-all-paths Trunc-level _ e)) {!!}
            
    short-span : Span {ℓ} {ℓ} {ℓ}
    short-span = span A W'.BMPushout A' fst W'.bmleft

    short-span-is-mono : is-mono (Span.f short-span)
    short-span-is-mono = λ b → equiv-preserves-level ((hfiber-fst b) ⁻¹) Trunc-level

    module PS = PushoutLSplit {A = A'} {B = A} {C = B} {D = D} fst fst (fst ∘ snd)
    module ML = MonoLemma short-span short-span-is-mono

    psplit-eqv : Pushout long-span ≃ Pushout short-span
    psplit-eqv = PS.split-equiv

    mono-conclusion : A' ≃ Σ (A × W'.BMPushout) (λ aw → ML.mleft (fst aw) == ML.mright (snd aw))
    mono-conclusion = ML.pushout-mono-is-pullback 

    module PBS₀ = PullbackLSplit {A = W'.BMPushout} {B = B} {C = A} {D = Pushout short-span} right right left
    module PBS₁ = PullbackLSplit {A = W'.BMPushout} {B = B} {C = A} {D = Pushout long-span} ((<– psplit-eqv) ∘ right) right left

    lower-cospan : Cospan 
    lower-cospan = cospan A W'.BMPushout (Pushout short-span) left right

    outer-cospan : Cospan 
    outer-cospan = cospan A B (Pushout short-span) left (right ∘ W'.bmright)

    -- Great.  And this one will be okay because of the
    -- equivalence that you prove above.
    outer-cospan' : Cospan
    outer-cospan' = cospan A B (Pushout long-span) left right
    
    upper-cospan : Cospan 
    upper-cospan = cospan (Pullback lower-cospan) B W'.BMPushout Pullback.b right

    upper-cospan' : Cospan
    upper-cospan' = cospan A' B W'.BMPushout W'.bmleft W'.bmright
    
    pb-conclusion : Pullback outer-cospan ≃ Pullback upper-cospan
    pb-conclusion = PBS₀.split-equiv

    --     L --> B    K = A ×_D C / (f,h)       d₁ = A -> D <- C
    --     |     |g   L = B ×_A K / (g,left)    d₂ = B -> A <- K
    --     v     v                              d  = B -> D <- C
    --     K --> A
    --     |     |f
    --     v     v
    --     C --> D
    --        h
