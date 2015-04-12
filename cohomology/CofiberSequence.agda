{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import cohomology.FlipPushout

module cohomology.CofiberSequence {i} where

{- Lemma: pushing flip-susp through susp-fmap -}
flip-susp-fmap : {A B : Type i} (f : A → B)
  → ∀ σ → flip-susp (susp-fmap f σ) == susp-fmap f (flip-susp σ)
flip-susp-fmap f = Suspension-elim _ idp idp $ λ y → ↓-='-in $
  ap-∘ (susp-fmap f) flip-susp (merid _ y)
  ∙ ap (ap (susp-fmap f)) (FlipSusp.glue-β y)
  ∙ ap-! (susp-fmap f) (merid _ y)
  ∙ ap ! (SuspFmap.glue-β f y)
  ∙ ! (FlipSusp.glue-β (f y))
  ∙ ! (ap (ap flip-susp) (SuspFmap.glue-β f y))
  ∙ ∘-ap flip-susp (susp-fmap f) (merid _ y)

{- Useful abbreviations -}
module _ {X Y : Ptd i} (f : fst (X ⊙→ Y)) where

  ⊙Cof² = ⊙Cof (⊙cfcod f)
  ⊙cfcod² = ⊙cfcod (⊙cfcod f)
  cfcod² = fst ⊙cfcod²
  ⊙Cof³ = ⊙Cof ⊙cfcod²
  ⊙cfcod³ = ⊙cfcod ⊙cfcod²
  cfcod³ = fst ⊙cfcod³

{- For [f : X → Y], the cofiber space [Cof(cfcod f)] is equivalent to
 - [Suspension X]. This is essentially an application of the two pushouts
 - lemma:
 -
 -       f
 -   X ––––> Y ––––––––––––––> ∙
 -   |       |                 |
 -   |       |cfcod f          |
 -   v       v                 v
 -   ∙ ––> Cof f ––––––––––> Cof² f
 -                cfcod² f
 -
 - The map [cfcod² f : Cof f → Cof² f] becomes [ext-glue : Cof f → ΣX],
 - and the map [ext-glue : Cof² f → ΣY] becomes [susp-fmap f : ΣX → ΣY].
 -}
module Cof² {X Y : Ptd i} (f : fst (X ⊙→ Y)) where

  module Equiv {X Y : Ptd i} (f : fst (X ⊙→ Y)) where

    module Into = CofiberRec (cfcod (fst f)) {C = fst (⊙Susp X)}
      (south _) ext-glue (λ _ → idp)

    into = Into.f

    ⊙into : fst (⊙Cof² f ⊙→ ⊙Susp X)
    ⊙into = (into , ! (merid _ (snd X)))

    module Out = SuspensionRec (fst X) {C = fst (⊙Cof² f)}
      (cfcod _ (cfbase _)) (cfbase _)
      (λ x → ap (cfcod _) (cfglue _ x) ∙ ! (cfglue _ (fst f x)))

    out = Out.f

    into-out : ∀ σ → into (out σ) == σ
    into-out = Suspension-elim (fst X) idp idp
      (λ x → ↓-∘=idf-in into out $
        ap (ap into) (Out.glue-β x)
        ∙ ap-∙ into (ap (cfcod _) (cfglue _ x)) (! (cfglue _ (fst f x)))
        ∙ ap (λ w → ap into (ap (cfcod _) (cfglue _ x)) ∙ w)
             (ap-! into (cfglue _ (fst f x)) ∙ ap ! (Into.glue-β (fst f x)))
        ∙ ∙-unit-r _
        ∙ ∘-ap into (cfcod _) (cfglue _ x) ∙ ExtGlue.glue-β x)

    out-into : ∀ κ → out (into κ) == κ
    out-into = Cofiber-elim (cfcod (fst f))
      idp
      (Cofiber-elim (fst f) idp (cfglue _)
        (λ x → ↓-='-from-square $
          (ap-∘ out ext-glue (cfglue _ x)
           ∙ ap (ap out) (ExtGlue.glue-β x) ∙ Out.glue-β x)
          ∙v⊡ (vid-square {p = ap (cfcod _) (cfglue _ x)}
               ⊡h rt-square (cfglue _ (fst f x)))
          ⊡v∙ ∙-unit-r _))
      (λ y → ↓-∘=idf-from-square out into $
         ap (ap out) (Into.glue-β y) ∙v⊡ connection)

    eq = equiv into out into-out out-into

    space-path : ⊙Cof² f == ⊙Susp X
    space-path = ⊙ua (⊙ify-eq eq (! (merid _ (snd X))))

  cfcod²-over : cfcod² f == ext-glue
                [ (λ U → fst (⊙Cof f) → fst U) ↓ Equiv.space-path f ]
  cfcod²-over = ↓-cst2-in _ _ $ codomain-over-equiv (cfcod² f) _

  cfcod³-over : ext-glue == flip-susp ∘ susp-fmap (fst f)
                [ (λ U → fst U → fst (⊙Susp Y)) ↓ Equiv.space-path f ]
  cfcod³-over = ↓-cst2-in _ _ $
    domain!-over-equiv ext-glue _ ▹ λ= lemma
    where
    lemma : (σ : fst (⊙Susp X))
      → ext-glue (Equiv.out f σ) == flip-susp (susp-fmap (fst f) σ)
    lemma = Suspension-elim (fst X) idp idp
      (λ x → ↓-='-in $
        ap-∘ flip-susp (susp-fmap (fst f)) (merid _ x)
        ∙ ap (ap flip-susp) (SuspFmap.glue-β (fst f) x)
        ∙ FlipSusp.glue-β (fst f x)
        ∙ ! (ap-∘ ext-glue (Equiv.out f) (merid _ x)
             ∙ ap (ap ext-glue) (Equiv.Out.glue-β f x)
             ∙ ap-∙ ext-glue (ap (cfcod _) (cfglue _ x))
                             (! (cfglue _ (fst f x)))
             ∙ (∘-ap ext-glue (cfcod _) (cfglue _ x)
                ∙ ap-cst (south _) (cfglue _ x))
               ∙2
               (ap-! ext-glue (cfglue _ (fst f x))
                ∙ ap ! (ExtGlue.glue-β (fst f x)))))

  open Equiv f public

cofiber-sequence : {X Y : Ptd i} (f : fst (X ⊙→ Y)) → Path
  {A = Σ (Ptd i × Ptd i)
         (λ {(U , V) → (fst (⊙Cof f) → fst U) × (fst U → fst V)})}
  ((⊙Cof² f , ⊙Cof³ f) , cfcod² f , cfcod³ f)
  ((⊙Susp X , ⊙Susp Y) , ext-glue , susp-fmap (fst f))
cofiber-sequence {X} {Y} f =
    ap (λ {(Z , g) → ((⊙Cof² f , Z) , cfcod² f , g)})
       (pair= (Cof².space-path (⊙cfcod f)) (Cof².cfcod²-over (⊙cfcod f)))
  ∙ ap (λ {(Z , g , h) → ((Z , ⊙Susp Y) , g , h)})
       (pair= (Cof².space-path f)
         (↓-×-in (Cof².cfcod²-over f) (Cof².cfcod³-over f)))
  ∙ ap (λ {(Z , g) → ((⊙Susp X , Z) , ext-glue , g)})
       (pair= (flip-⊙pushout-path (suspension-⊙span Y))
              (↓-cst2-in _ _ $ codomain!-over-equiv _ _))
