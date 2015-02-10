{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import cohomology.FlipPushout

module cohomology.CofiberSequence {i} where

{- Lemma: pushing flip-susp through susp-fmap -}
⊙flip-susp-fmap : {X Y : Ptd i} (f : fst (X ⊙→ Y))
  → ⊙flip-susp Y ⊙∘ ⊙susp-fmap f == ⊙susp-fmap f ⊙∘ ⊙flip-susp X
⊙flip-susp-fmap {X = X} (f , idp) = ⊙λ= lemma-fst lemma-snd
  where
  lemma-fst : ∀ σ →
    flip-susp (susp-fmap f σ) == susp-fmap f (flip-susp σ)
  lemma-fst = Suspension-elim _ idp idp $ λ y → ↓-='-in $
    ap-∘ (susp-fmap f) flip-susp (merid _ y)
    ∙ ap (ap (susp-fmap f)) (FlipSusp.glue-β y)
    ∙ ap-! (susp-fmap f) (merid _ y)
    ∙ ap ! (SuspFmap.glue-β f y)
    ∙ ! (FlipSusp.glue-β (f y))
    ∙ ! (ap (ap flip-susp) (SuspFmap.glue-β f y))
    ∙ ∘-ap flip-susp (susp-fmap f) (merid _ y)

  lemma-snd :
    ! (merid _ (f (snd X))) == ap (susp-fmap f) (! (merid _ (snd X))) ∙ idp
  lemma-snd =
     ap ! (! (SuspFmap.glue-β f (snd X)))
     ∙ !-ap (susp-fmap f) (merid _ (snd X))
     ∙ ! (∙-unit-r _)

{- Useful abbreviations -}
module _ {X Y : Ptd i} (f : fst (X ⊙→ Y)) where

  ⊙Cof² = ⊙Cof (⊙cfcod f)
  ⊙cfcod² = ⊙cfcod (⊙cfcod f)
  ⊙Cof³ = ⊙Cof ⊙cfcod²
  ⊙cfcod³ = ⊙cfcod ⊙cfcod²
  ⊙Cof⁴ = ⊙Cof ⊙cfcod³
  ⊙cfcod⁴ = ⊙cfcod ⊙cfcod³

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
               ⊡h ru-square (cfglue _ (fst f x)))
          ⊡v∙ ∙-unit-r _))
      (λ y → ↓-∘=idf-from-square out into $
         ap (ap out) (Into.glue-β y) ∙v⊡ connection)

    eq = equiv into out into-out out-into

    space-path : ⊙Cof² f == ⊙Susp X
    space-path = ⊙ua eq (! (merid _ (snd X)))

  cfcod²-over : ⊙cfcod² f == ⊙ext-glue
                [ (λ U → fst (⊙Cof f ⊙→ U)) ↓ Equiv.space-path f ]
  cfcod²-over = ind-lemma f
    where
    {- is there a better way to handle this? -}
    ind-lemma : {X Y : Ptd i} (f : fst (X ⊙→ Y))
      → ⊙cfcod² f == ⊙ext-glue
        [ (λ U → fst (⊙Cof f ⊙→ U)) ↓ Equiv.space-path f ]
    ind-lemma {X = X} (f , idp) =
      codomain-over-⊙equiv (⊙cfcod² (f , idp)) _ _
      ▹ pair= idp (l snd-lemma)
      where
      x₀ = snd X; y₀ = f (snd X); F = (f , idp {a = y₀})

      snd-lemma : ap (Equiv.into F)
                     (ap (cfcod (cfcod f)) (! (! (cfglue _ x₀)))
                      ∙ ! (cfglue _ y₀))
                  == merid _ x₀
      snd-lemma =
        ap (Equiv.into F)
           (ap (cfcod (cfcod f)) (! (! (cfglue _ x₀))) ∙ ! (cfglue _ y₀))
          =⟨ !-! (cfglue _ x₀) |in-ctx (λ w →
               ap (Equiv.into F) (ap (cfcod (cfcod f)) w ∙ ! (cfglue _ y₀))) ⟩
        ap (Equiv.into F)
           (ap (cfcod (cfcod f)) (cfglue _ x₀) ∙ ! (cfglue _ y₀))
          =⟨ ap-∙ (Equiv.into F)
               (ap (cfcod (cfcod f)) (cfglue _ x₀)) (! (cfglue _ y₀)) ⟩
        ap (Equiv.into F) (ap (cfcod (cfcod f)) (cfglue _ x₀))
        ∙ ap (Equiv.into F) (! (cfglue _ y₀))
          =⟨ ∘-ap (Equiv.into F) (cfcod (cfcod f)) (cfglue _ x₀)
             |in-ctx (λ w → w ∙ ap (Equiv.into F) (! (cfglue _ y₀))) ⟩
        ap ext-glue (cfglue _ x₀) ∙ ap (Equiv.into F) (! (cfglue _ y₀))
          =⟨ ExtGlue.glue-β x₀
             |in-ctx (λ w → w ∙ ap (Equiv.into F) (! (cfglue _ y₀))) ⟩
        merid _ x₀ ∙ ap (Equiv.into F) (! (cfglue _ y₀))
          =⟨ ap-! (Equiv.into F) (cfglue _ y₀) |in-ctx (λ w → merid _ x₀ ∙ w) ⟩
        merid _ x₀ ∙ ! (ap (Equiv.into F) (cfglue _ y₀))
          =⟨ Equiv.Into.glue-β F y₀ |in-ctx (λ w → merid _ x₀ ∙ ! w) ⟩
        merid _ x₀ ∙ idp
          =⟨ ∙-unit-r _ ⟩
        merid _ x₀ ∎

      l : ∀ {i} {A : Type i} {x y : A} {p q : x == y}
        → p == q → p ∙ ! q == idp
      l {p = p} {q = q} α = ap (λ r → r ∙ ! q) α ∙ !-inv-r q

  cfcod³-over :
    ⊙ext-glue == ⊙flip-susp Y ⊙∘ ⊙susp-fmap f
    [ (λ U → fst (U ⊙→ ⊙Susp Y)) ↓ Equiv.space-path f ]
  cfcod³-over =
    ⊙λ= fst-lemma (l snd-lemma)
    ◃ domain-over-⊙equiv (⊙flip-susp Y ⊙∘ ⊙susp-fmap f) _ _
    where
    fst-lemma : (κ : fst (⊙Cof² f))
      → ext-glue κ == flip-pushout (susp-fmap (fst f) (Equiv.into f κ))
    fst-lemma = Cofiber-elim (cfcod (fst f))
      idp
      (Cofiber-elim (fst f)
        idp
        (! ∘ merid (fst Y))
        (λ x → ↓-='-from-square $
          ap-cst (south _) (cfglue _ x) ∙v⊡
            connection
          ⊡v∙ ! (ap-∘ (flip-pushout ∘ susp-fmap (fst f)) ext-glue (cfglue _ x)
                 ∙ ap (ap (flip-pushout ∘ susp-fmap (fst f))) (ExtGlue.glue-β x)
                 ∙ ap-∘ flip-pushout (susp-fmap (fst f)) (merid _ x)
                 ∙ ap (ap flip-pushout) (SuspFmap.glue-β (fst f) x)
                 ∙ FlipPushout.glue-β (fst f x))))
      (λ y → ↓-='-from-square $
        ExtGlue.glue-β y ∙v⊡
          ur-square (merid _ y)
        ⊡v∙ ! (ap-∘ (flip-pushout ∘ susp-fmap (fst f)) (Equiv.into f)
                    (cfglue _ y)
               ∙ ap (ap (flip-pushout ∘ susp-fmap (fst f)))
                    (Equiv.Into.glue-β f y)))

    snd-lemma : ap (flip-pushout ∘ susp-fmap (fst f)) (! (merid _ (snd X)))
                == merid _ (snd Y)
    snd-lemma =
      ap (flip-pushout ∘ susp-fmap (fst f)) (! (merid _ (snd X)))
        =⟨ ap-! (flip-pushout ∘ susp-fmap (fst f)) (merid _ (snd X)) ⟩
      ! (ap (flip-pushout ∘ susp-fmap (fst f)) (merid _ (snd X)))
        =⟨ ap ! (ap-∘ flip-pushout (susp-fmap (fst f)) (merid _ (snd X))) ⟩
      ! (ap flip-pushout (ap (susp-fmap (fst f)) (merid _ (snd X))))
        =⟨ ap (! ∘ ap flip-pushout) (SuspFmap.glue-β (fst f) (snd X)) ⟩
      ! (ap flip-pushout (merid _ (fst f (snd X))))
        =⟨ ap ! (FlipPushout.glue-β (fst f (snd X))) ⟩
      ! (! (merid _ (fst f (snd X))))
        =⟨ !-! (merid _ (fst f (snd X))) ⟩
      merid _ (fst f (snd X))
        =⟨ ap (merid _) (snd f) ⟩
      merid _ (snd Y) ∎

    l : ∀ {i} {A : Type i} {x y : A} {p q : x == y}
      → p == q → idp == p ∙ ! q
    l {p = p} {q = q} α = ! (!-inv-r p) ∙ ap (λ w → p ∙ ! w) α

  open Equiv f public

  full-path : Path
    {A = Σ (Ptd i) (λ U → fst (⊙Cof f ⊙→ U) × fst (U ⊙→ ⊙Susp Y))}
    (_ , ⊙cfcod² f , ⊙ext-glue)
    (_ , ⊙ext-glue , ⊙flip-susp Y ⊙∘ ⊙susp-fmap f)
  full-path = pair= space-path (↓-×-in cfcod²-over cfcod³-over)

cofiber-sequence : {X Y : Ptd i} (f : fst (X ⊙→ Y)) → Path
  {A = Σ (Ptd i × Ptd i × Ptd i)
         (λ {(U , V , W) → fst (⊙Cof f ⊙→ U) × fst (U ⊙→ V) × fst (V ⊙→ W)})}
  (_ , ⊙cfcod² f , ⊙cfcod³ f , ⊙cfcod⁴ f)
  (_ , ⊙ext-glue , ⊙susp-fmap f , ⊙susp-fmap (⊙cfcod f))
cofiber-sequence {Y = Y} f =
    ap (λ {(_ , g , _) → (_ , ⊙cfcod² f , ⊙cfcod³ f , g)})
       (Cof².full-path (⊙cfcod² f))
  ∙ ap (λ {(_ , g , h) → (_ , ⊙cfcod² f , g , h)})
       (Cof².full-path (⊙cfcod f))
  ∙ ap (λ {(_ , g , h) → (_ , g , h , ⊙flip-susp (⊙Cof f) ⊙∘
                                      ⊙susp-fmap (⊙cfcod f))})
       (Cof².full-path f)
  ∙ ap (λ g → (_ , ⊙ext-glue , ⊙flip-susp Y ⊙∘ ⊙susp-fmap f , g))
       (⊙flip-susp-fmap (⊙cfcod f))
  ∙ ap (λ {(_ , g , h) → (_ , ⊙ext-glue , g , h)})
       (pair= (flip-⊙pushout-path (suspension-⊙span Y))
          (↓-×-in (codomain-over-⊙equiv
                    (⊙flip-susp Y ⊙∘ ⊙susp-fmap f) _ _
                   ▹ lemma)
                  (domain-over-⊙equiv (⊙susp-fmap (⊙cfcod f)) _ _)))
  where
  lemma : ⊙flip-susp Y ⊙∘ ⊙flip-susp Y ⊙∘ ⊙susp-fmap f
       == ⊙susp-fmap f
  lemma = ! (⊙∘-assoc (⊙flip-susp Y) (⊙flip-susp Y) (⊙susp-fmap f))
          ∙ ap (λ w → w ⊙∘ ⊙susp-fmap f)
               (flip-⊙pushout-involutive (suspension-⊙span Y))
          ∙ ⊙∘-unit-l (⊙susp-fmap f)

suspend-cofiber : {X Y : Ptd i} (f : fst (X ⊙→ Y)) → Path
  {A = Σ _ (λ {(U , V , W) → fst (U ⊙→ V) × fst (V ⊙→ W)})}
  (_ , ⊙susp-fmap f , ⊙cfcod (⊙susp-fmap f))
  (_ , ⊙susp-fmap f , ⊙susp-fmap (⊙cfcod f))
suspend-cofiber f =
  ap (λ {((U , V , W) , _ , g , _) → ((U , V , ⊙Cof g) , g , ⊙cfcod g)})
     (! (cofiber-sequence f))
  ∙ ap (λ {(_ , _ , g , h) → (_ , g , h)}) (cofiber-sequence f)

suspend^-cof= : {X Y Z : Ptd i} (m : ℕ) (f : fst (X ⊙→ Y)) (g : fst (Y ⊙→ Z))
  (p : Path {A = Σ _ (λ U → fst (Y ⊙→ U))} (⊙Cof f , ⊙cfcod f) (Z , g))
  → Path {A = Σ _ (λ {(U , V , W) → fst (U ⊙→ V) × fst (V ⊙→ W)})}
    (_ , ⊙susp^-fmap m f , ⊙cfcod (⊙susp^-fmap m f))
    (_ , ⊙susp^-fmap m f , ⊙susp^-fmap m g)
suspend^-cof= O f g p = ap (λ {(_ , h) → (_ , f , h)}) p
suspend^-cof= (S m) f g p =
  suspend-cofiber (⊙susp^-fmap m f)
  ∙ ap (λ {(_ , h , k) → (_ , ⊙susp-fmap h , ⊙susp-fmap k)})
       (suspend^-cof= m f g p)
