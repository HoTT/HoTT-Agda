{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import cohomology.FlipPushout
open import cohomology.TwoPushouts

module cohomology.CofiberSequence {i} {X Y : Ptd i} (f : fst (X ∙→ Y))
  where

{- Introduce some abbreviations -}
private
  ptd-span² = ptd-cof-span (ptd-cfcod f)
  Ptd-Cof² = Ptd-Cof (ptd-cfcod f)
  ptd-cfcod² = ptd-cfcod (ptd-cfcod f)
  ptd-span³ = ptd-cof-span ptd-cfcod²
  Ptd-Cof³ = Ptd-Cof ptd-cfcod²
  ptd-cfcod³ = ptd-cfcod ptd-cfcod²

{- Define the coboundary mapping from Cof(f) to ΣX -}
module Co∂ = CofiberRec (fst f)
  (north (fst X))
  (λ _ → south (fst X))
  (merid (fst X))

co∂ = Co∂.f

ptd-co∂ : fst (Ptd-Cof f ∙→ Ptd-Susp X)
ptd-co∂ = (co∂ , idp)

private

  {- Two pushouts lemma for the diagram:
   -
   -       f
   -   X ––––> Y –––––––––> ∙
   -   |       |            |
   -   |       |cod(f)      |
   -   v       v            v
   -   ∙ ––> Cof(f) ––> Flip(Cof²(f))
   -
   - The right cofiber pushout needs to be flipped to fit in the diagram.
   -}
  module 2PDom = TwoPushoutsPtd
    (ptd-cst {X = X} {Y = Ptd-Unit}) f (ptd-cst {X = Y} {Y = Ptd-Unit})


{- The functions susp-to-cof² and cof²-to-susp are intermediate mappings
 - that appear in the course of proof. These are elimated in the final
 - result by the equality [resolve] which shows that
 - flip-pushout ∘ cof²-to-susp ∘ susp-to-cof² == susp-fmap (fst f) -}

ptd-susp-to-cof² : fst (Ptd-Susp X ∙→ Ptd-Cof²)
ptd-susp-to-cof² =
  flip-ptd-pushout (flip-ptd-span ptd-span²) ∘ptd (2PDom.into , idp)

susp-to-cof² = fst ptd-susp-to-cof²

cof²-to-susp : fst Ptd-Cof² → fst (Ptd-Susp Y)
cof²-to-susp = CofiberRec.f _
  (north _)
  (λ _ → south _)
  (merid _)

ptd-cof²-to-susp : fst (Ptd-Cof² ∙→ Ptd-Susp Y)
ptd-cof²-to-susp = (cof²-to-susp , idp)

private
  resolve : flip-ptd-pushout (suspension-ptd-span Y)
            ∘ptd ptd-cof²-to-susp ∘ptd ptd-susp-to-cof²
            == ptd-susp-fmap f
  resolve = pair= (λ= first) second
    where
    first : ∀ σ → flip-pushout (cof²-to-susp (susp-to-cof² σ))
               == susp-fmap (fst f) σ
    first = Suspension-elim (fst X) idp idp $ λ x → ↓-='-in $
      ap (susp-fmap (fst f)) (merid _ x)
        =⟨ SuspFmap.glue-β (fst f) x ⟩
      merid _ (fst f x)
        =⟨ ! (!-! (merid _ (fst f x))) ⟩
      ! (! (merid _ (fst f x)))
        =⟨ ! (FlipPushout.glue-β (fst f x)) |in-ctx ! ⟩
      ! (ap flip-pushout (merid _ (fst f x)))
        =⟨ ! (CofiberRec.glue-β _ _ _ _ (fst f x))
           |in-ctx (λ w → ! (ap flip-pushout w)) ⟩
      ! (ap flip-pushout (ap cof²-to-susp (cfglue _ (fst f x))))
        =⟨ ∘-ap flip-pushout cof²-to-susp (cfglue _ (fst f x)) |in-ctx ! ⟩
      ! (ap (flip-pushout ∘ cof²-to-susp) (cfglue _ (fst f x)))
        =⟨ !-ap (flip-pushout ∘ cof²-to-susp) (cfglue _ (fst f x)) ⟩
      ap (flip-pushout ∘ cof²-to-susp) (! (cfglue _ (fst f x)))
        =⟨ ! (FlipPushout.glue-β (fst f x))
           |in-ctx (λ w → ap (flip-pushout ∘ cof²-to-susp) w) ⟩
      ap (flip-pushout ∘ cof²-to-susp) (ap flip-pushout (glue (fst f x)))
        =⟨ ∘-ap (flip-pushout ∘ cof²-to-susp) flip-pushout (glue (fst f x)) ⟩
      ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) (glue (fst f x))
        =⟨ ! (ap-cst (north _) (glue x))
           |in-ctx (λ w → w ∙ ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout)
                                 (glue (fst f x))) ⟩
      ap (λ _ → north _) (glue x)
      ∙ ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) (glue (fst f x))
        =⟨ ap-∘ (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) left (glue x)
           |in-ctx (λ w → w ∙ ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout)
                                 (glue (fst f x))) ⟩
      ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) (ap left (glue x))
      ∙ ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) (glue (fst f x))
        =⟨ ∙-ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout)
                 (ap left (glue x)) (glue (fst f x)) ⟩
      ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout)
         (ap left (glue x) ∙ glue (fst f x))
        =⟨ ! (2PDom.Into.glue-β x)
           |in-ctx (λ w → ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) w) ⟩
      ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout)
         (ap 2PDom.into (merid _ x))
        =⟨ ∘-ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout) 2PDom.into
                (merid _ x) ⟩
      ap (flip-pushout ∘ cof²-to-susp ∘ flip-pushout ∘ 2PDom.into) (merid _ x) ∎

    second : snd (flip-ptd-pushout (suspension-ptd-span Y)
                  ∘ptd ptd-cof²-to-susp ∘ptd ptd-susp-to-cof²)
             == idp
             [ (λ h → h (north _) == north _) ↓ (λ= first) ]
    second = ↓-app=cst-in $
      snd (flip-ptd-pushout (suspension-ptd-span Y)
            ∘ptd ptd-cof²-to-susp
            ∘ptd ptd-susp-to-cof²)
        =⟨ idp ⟩
      ap flip-pushout
         (ap cof²-to-susp
             (ap (cfcod _) abbr
              ∙ ! (cfglue _ (snd Y)))
          ∙ idp)
      ∙ ! (merid _ (snd Y))
        =⟨ ∙-unit-r (ap cof²-to-susp (ap (cfcod _) abbr ∙ ! (cfglue _ (snd Y))))
           |in-ctx (λ w → ap flip-pushout w ∙ ! (merid _ (snd Y))) ⟩
      ap flip-pushout
         (ap cof²-to-susp
             (ap (cfcod _) abbr ∙ ! (cfglue _ (snd Y))))
      ∙ ! (merid _ (snd Y))
        =⟨ ap-∙ cof²-to-susp (ap (cfcod _) abbr) (! (cfglue _ (snd Y)))
           |in-ctx (λ w → ap flip-pushout w ∙ ! (merid _ (snd Y))) ⟩
      ap flip-pushout
         (ap cof²-to-susp (ap (cfcod _) abbr)
          ∙ ap cof²-to-susp (! (cfglue _ (snd Y))))
      ∙ ! (merid _ (snd Y))
        =⟨ ∘-ap cof²-to-susp (cfcod _) abbr ∙ ap-cst (south _) abbr
           |in-ctx (λ w → ap flip-pushout
                             (w ∙ ap cof²-to-susp (! (cfglue _ (snd Y))))
                          ∙ ! (merid _ (snd Y))) ⟩
      ap flip-pushout (ap cof²-to-susp (! (cfglue _ (snd Y))))
      ∙ ! (merid _ (snd Y))
        =⟨ ap-! cof²-to-susp (cfglue _ (snd Y))
           |in-ctx (λ w → ap flip-pushout w ∙ ! (merid _ (snd Y))) ⟩
      ap flip-pushout (! (ap cof²-to-susp (cfglue _ (snd Y))))
      ∙ ! (merid _ (snd Y))
        =⟨ CofiberRec.glue-β _ _ _ _ (snd Y)
           |in-ctx (λ w → ap flip-pushout (! w) ∙ ! (merid _ (snd Y))) ⟩
      ap flip-pushout (! (merid _ (snd Y))) ∙ ! (merid _ (snd Y))
        =⟨ ap-! flip-pushout (merid _ (snd Y))
           |in-ctx (λ w → w ∙ ! (merid _ (snd Y))) ⟩
      ! (ap flip-pushout (merid _ (snd Y))) ∙ ! (merid _ (snd Y))
        =⟨ FlipPushout.glue-β (snd Y)
           |in-ctx (λ w → ! w ∙ ! (merid _ (snd Y))) ⟩
      ! (! (merid _ (snd Y))) ∙ ! (merid _ (snd Y))
        =⟨ !-inv-l (! (merid _ (snd Y))) ⟩
      idp
        =⟨ ! (app=-β first (north _)) |in-ctx (λ w → w ∙ idp) ⟩
      app= (λ= first) (north _) ∙ idp ∎
      where
      -- the structure of this subterm is irrelevant to the proof,
      -- so we'll save some space by abbreviating it
      abbr = ! (ap (cfcod _) (! (snd f)) ∙ ! (cfglue _ (snd X)))


  {- FIRST MAIN PATH: Proof that [Cof²(f) == ΣX].
   - We also compute the effect of this path on the functions
   - [cfcod²(f) : Cof(f) → Cof²(f)], which is taken to [co∂ : Cof(f) → ΣX],
   - and [cfcod³(f) : Cof²(f) → Cof³(f)], which is taken to the intermediate
   - function [cfcod³ ∘ susp-to-cof²].
   -}
  cof²-is-susp-dom : Path
    {A = Σ (Ptd i)
           (λ W → fst (Ptd-Cof f ∙→ W) × fst (W ∙→ Ptd-Cof³))}
    (Ptd-Cof² , ptd-cfcod² , ptd-cfcod³)
    (Ptd-Susp X , ptd-co∂ , ptd-cfcod³ ∘ptd ptd-susp-to-cof²)

  cof²-is-susp-dom =
    (Ptd-Cof² , ptd-cfcod² , ptd-cfcod³)
      =⟨ pair= (flip-ptd-pushout-path ptd-span²)
               (↓-×-in (flip-ptd-right ptd-span²) prepend-flip) ⟩
    (Ptd-Pushout (flip-ptd-span ptd-span²) ,
     ptd-left {d = flip-ptd-span ptd-span²} ,
     ptd-cfcod³ ∘ptd flip-ptd-pushout (flip-ptd-span ptd-span²))
      =⟨ ! (pair= 2PDom.two-pushouts-ptd
                  (↓-×-in 2PDom.two-pushouts-ptd-inner
                          (ap↓ (λ w → ptd-cfcod³ ∘ptd w)
                               (domain-over-ptd-equiv
                                 (flip-ptd-pushout (flip-ptd-span ptd-span²))
                                                   _ _)))) ⟩
    (Ptd-Lift {j = i} (Ptd-Pushout (suspension-ptd-span X)) ,
     ptd-lift ∘ptd ptd-co∂ ,
     ptd-cfcod³ ∘ptd ptd-susp-to-cof² ∘ptd ptd-lower)
      =⟨ pair= (ptd-ua lift-equiv idp)
               (↓-×-in (codomain!-over-ptd-equiv ptd-co∂ _ _)
                       (domain-over-ptd-equiv
                         (ptd-cfcod³ ∘ptd ptd-susp-to-cof²) _ _)) ⟩
    (Ptd-Susp X , ptd-co∂ ,
     ptd-cfcod³ ∘ptd ptd-susp-to-cof²) ∎
    where
    prepend-flip-lemma :
      (flip-pushout ,
       ap flip-pushout (! (snd (ptd-right {d = flip-ptd-span ptd-span²})))
       ∙ idp)
      == (flip-ptd-pushout (flip-ptd-span ptd-span²))
    prepend-flip-lemma = pair= idp $
      ap flip-pushout (! (snd (ptd-right {d = flip-ptd-span ptd-span²})))
      ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap flip-pushout (! (snd (ptd-right {d = flip-ptd-span ptd-span²})))
        =⟨ ap-! flip-pushout (snd (ptd-right {d = flip-ptd-span ptd-span²})) ⟩
      ! (ap flip-pushout (snd (ptd-right {d = flip-ptd-span ptd-span²})))
        =⟨ ap-flip-right (flip-ptd-span ptd-span²) |in-ctx ! ⟩
      ! (! (snd (ptd-right {d = ptd-span²})))
        =⟨ !-! (snd (ptd-right {d = ptd-span²})) ⟩
      snd (ptd-right {d = ptd-span²}) ∎

    prepend-flip :
      ptd-cfcod³ == (ptd-cfcod³ ∘ptd flip-ptd-pushout (flip-ptd-span ptd-span²))
      [ (λ W → fst (W ∙→ Ptd-Cof³)) ↓ flip-ptd-pushout-path ptd-span² ]
    prepend-flip =
      domain!-over-ptd-equiv _ _ _
      ▹ ap (λ w → ptd-cfcod³ ∘ptd w) prepend-flip-lemma


  {- Two pushouts lemma for the diagram:
   -
   -     cod(f)
   -   Y ––––> Cof(f) ––––––> ∙
   -   |         |            |
   -   |         |cod²(f)     |
   -   v         v            v
   -   ∙ –––> Cof²(f) ––> Flip(Cof³(f))
   -
   - The right cofiber pushout needs to be flipped to fit.
   -}
  module 2PCod = TwoPushoutsPtd
    (ptd-cst {X = Y} {Y = Ptd-Unit}) (ptd-cfcod f)
    (ptd-cst {X = Ptd-Cof f} {Y = Ptd-Unit})


{- SECOND MAIN PATH: Proof that [Cof³(f) == ΣY].
 - We also compute the effect of this path on the function
 - [cfcod³(f) : Cof²(f) → Cof³(f)], which is taken to
 - the intermediate function [ptd-cof²-to-susp : Cof²(f) → ΣY],
 -}
cof³-is-susp-cod : Path
  {A = Σ (Ptd i) (λ W → fst (Ptd-Cof² ∙→ W))}
  (Ptd-Cof³ , ptd-cfcod³)
  (Ptd-Susp Y , ptd-cof²-to-susp)
cof³-is-susp-cod =
  (Ptd-Cof³ , ptd-cfcod³)
    =⟨ pair= (flip-ptd-pushout-path ptd-span³) (flip-ptd-right ptd-span³) ⟩
  (Ptd-Pushout (flip-ptd-span ptd-span³) ,
   ptd-left {d = flip-ptd-span ptd-span³})
    =⟨ ! (pair= 2PCod.two-pushouts-ptd 2PCod.two-pushouts-ptd-inner) ⟩
  (Ptd-Lift {j = i} (Ptd-Pushout (suspension-ptd-span Y)) ,
   ptd-lift ∘ptd ptd-cof²-to-susp)
    =⟨ pair= (ptd-ua lift-equiv idp)
             (codomain!-over-ptd-equiv ptd-cof²-to-susp _ _) ⟩
  (Ptd-Susp Y , ptd-cof²-to-susp) ∎


{- FIRST EXPORTED RESULT: Long Cofiber Sequence
 - The sequence
 -
 -      f    cod(f)        cod²(f)         cod³(f)
 -   X ––> Y –––––> Cof(f) ––––––> Cof²(f) ––––––> Cof³(f)
 -
 - is equal to the sequence
 -
 -      f    cod(f)          co∂             Σf
 -   X ––> Y –––––> Cof(f) ––––––>   ΣX    ––––––>   ΣY
 -}
cod-Σf-path : Path {A = Σ (Ptd i) (λ V → fst (Ptd-Susp X ∙→ V))}
  (Ptd-Cof³ , ptd-cfcod³ ∘ptd ptd-susp-to-cof²)
  (Ptd-Susp Y , ptd-susp-fmap f)
cod-Σf-path =
  (Ptd-Cof³ , ptd-cfcod³ ∘ptd ptd-susp-to-cof²)
    =⟨ ap (λ {(W , h) → (W , h ∘ptd ptd-susp-to-cof²)}) cof³-is-susp-cod ⟩
  (Ptd-Susp Y , ptd-cof²-to-susp ∘ptd ptd-susp-to-cof²)
    =⟨ pair= (flip-ptd-pushout-path (suspension-ptd-span Y))
              (codomain-over-ptd-equiv
                (ptd-cof²-to-susp ∘ptd ptd-susp-to-cof²) _ _) ⟩
  (Ptd-Susp Y , flip-ptd-pushout (suspension-ptd-span Y)
                ∘ptd ptd-cof²-to-susp ∘ptd ptd-susp-to-cof²)
    =⟨ ap (λ h → (Ptd-Susp Y , h)) resolve ⟩
  (Ptd-Susp Y , ptd-susp-fmap f) ∎

cofiber-sequence : Path
  {A = Σ (Ptd i × Ptd i)
         (λ {(U , V) → fst (Ptd-Cof f ∙→ U) × fst (U ∙→ V)})}
  ((Ptd-Cof² , Ptd-Cof³) , (ptd-cfcod² , ptd-cfcod³))
  ((Ptd-Susp X , Ptd-Susp Y) , (ptd-co∂ , ptd-susp-fmap f))

cofiber-sequence =
  ((Ptd-Cof² , Ptd-Cof³) , (ptd-cfcod² , ptd-cfcod³))
    =⟨ ap (λ {(W , (g , h)) → ((W , Ptd-Cof³) , (g , h))}) cof²-is-susp-dom ⟩
  ((Ptd-Susp X , Ptd-Cof³) , (ptd-co∂ , ptd-cfcod³ ∘ptd ptd-susp-to-cof²))
    =⟨ ap (λ {(W , h) → ((Ptd-Susp X , W) , (ptd-co∂ , h))}) cod-Σf-path ⟩
  ((Ptd-Susp X , Ptd-Susp Y) , (ptd-co∂ , ptd-susp-fmap f)) ∎


{- SECOND EXPORTED RESULT: Coboundary
 - This is probably deducible from the previous path, but it's easier
 - to do it with the private paths.
 -}
co∂-is-cfcod² : Path {A = Σ (Ptd i) (λ W → fst (Ptd-Cof f ∙→ W))}
  (Ptd-Cof² , ptd-cfcod²) (Ptd-Susp X , ptd-co∂)
co∂-is-cfcod² = ap (λ {(W , (h , _)) → (W , h)}) cof²-is-susp-dom
