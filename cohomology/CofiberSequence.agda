{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import cohomology.FlipPushout
open import cohomology.TwoPushouts

module cohomology.CofiberSequence {i} where

{- Lemma: pushing flip-susp through susp-fmap -}
ptd-flip-susp-fmap : {X Y : Ptd i} (f : fst (X ∙→ Y))
  → ptd-flip-susp Y ∘ptd ptd-susp-fmap f == ptd-susp-fmap f ∘ptd ptd-flip-susp X
ptd-flip-susp-fmap {X = X} (f , idp) = ptd-λ= lemma-fst lemma-snd
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
module _ {X Y : Ptd i} (f : fst (X ∙→ Y)) where

  Ptd-Cof² = Ptd-Cof (ptd-cfcod f)
  ptd-cfcod² = ptd-cfcod (ptd-cfcod f)
  Ptd-Cof³ = Ptd-Cof ptd-cfcod²
  ptd-cfcod³ = ptd-cfcod ptd-cfcod²
  Ptd-Cof⁴ = Ptd-Cof ptd-cfcod³
  ptd-cfcod⁴ = ptd-cfcod ptd-cfcod³

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
module Cof² {X Y : Ptd i} (f : fst (X ∙→ Y)) where

  module Equiv {X Y : Ptd i} (f : fst (X ∙→ Y)) where

    module Into = CofiberRec (cfcod (fst f)) {C = fst (Ptd-Susp X)}
      (south _) ext-glue (λ _ → idp)

    into = Into.f

    module Out = SuspensionRec (fst X) {C = fst (Ptd-Cof² f)}
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

    space-path : Ptd-Cof² f == Ptd-Susp X
    space-path = ptd-ua eq (! (merid _ (snd X)))

  cfcod²-over : ptd-cfcod² f == ptd-ext-glue
                [ (λ U → fst (Ptd-Cof f ∙→ U)) ↓ Equiv.space-path f ]
  cfcod²-over = ind-lemma f
    where
    {- is there a better way to handle this? -}
    ind-lemma : {X Y : Ptd i} (f : fst (X ∙→ Y))
      → ptd-cfcod² f == ptd-ext-glue
        [ (λ U → fst (Ptd-Cof f ∙→ U)) ↓ Equiv.space-path f ]
    ind-lemma {X = X} (f , idp) =
      codomain-over-ptd-equiv (ptd-cfcod² (f , idp)) _ _
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
    ptd-ext-glue == ptd-flip-susp Y ∘ptd ptd-susp-fmap f
    [ (λ U → fst (U ∙→ Ptd-Susp Y)) ↓ Equiv.space-path f ]
  cfcod³-over =
    ptd-λ= fst-lemma (l snd-lemma)
    ◃ domain-over-ptd-equiv (ptd-flip-susp Y ∘ptd ptd-susp-fmap f) _ _
    where
    fst-lemma : (κ : fst (Ptd-Cof² f))
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
    {A = Σ (Ptd i) (λ U → fst (Ptd-Cof f ∙→ U) × fst (U ∙→ Ptd-Susp Y))}
    (_ , ptd-cfcod² f , ptd-ext-glue)
    (_ , ptd-ext-glue , ptd-flip-susp Y ∘ptd ptd-susp-fmap f)
  full-path = pair= space-path (↓-×-in cfcod²-over cfcod³-over)

cofiber-sequence : {X Y : Ptd i} (f : fst (X ∙→ Y)) → Path
  {A = Σ (Ptd i × Ptd i × Ptd i)
         (λ {(U , V , W) → fst (Ptd-Cof f ∙→ U) × fst (U ∙→ V) × fst (V ∙→ W)})}
  (_ , ptd-cfcod² f , ptd-cfcod³ f , ptd-cfcod⁴ f)
  (_ , ptd-ext-glue , ptd-susp-fmap f , ptd-susp-fmap (ptd-cfcod f))
cofiber-sequence {Y = Y} f =
    ap (λ {(_ , g , _) → (_ , ptd-cfcod² f , ptd-cfcod³ f , g)})
       (Cof².full-path (ptd-cfcod² f))
  ∙ ap (λ {(_ , g , h) → (_ , ptd-cfcod² f , g , h)})
       (Cof².full-path (ptd-cfcod f))
  ∙ ap (λ {(_ , g , h) → (_ , g , h , ptd-flip-susp (Ptd-Cof f) ∘ptd
                                      ptd-susp-fmap (ptd-cfcod f))})
       (Cof².full-path f)
  ∙ ap (λ g → (_ , ptd-ext-glue , ptd-flip-susp Y ∘ptd ptd-susp-fmap f , g))
       (ptd-flip-susp-fmap (ptd-cfcod f))
  ∙ ap (λ {(_ , g , h) → (_ , ptd-ext-glue , g , h)})
       (pair= (flip-ptd-pushout-path (suspension-ptd-span Y))
          (↓-×-in (codomain-over-ptd-equiv
                    (ptd-flip-susp Y ∘ptd ptd-susp-fmap f) _ _
                   ▹ lemma)
                  (domain-over-ptd-equiv (ptd-susp-fmap (ptd-cfcod f)) _ _)))
  where
  lemma : ptd-flip-susp Y ∘ptd ptd-flip-susp Y ∘ptd ptd-susp-fmap f
       == ptd-susp-fmap f
  lemma = ! (∘ptd-assoc (ptd-flip-susp Y) (ptd-flip-susp Y) (ptd-susp-fmap f))
          ∙ ap (λ w → w ∘ptd ptd-susp-fmap f)
               (flip-ptd-pushout-involutive (suspension-ptd-span Y))
          ∙ ∘ptd-unit-l (ptd-susp-fmap f)

suspend-cofiber : {X Y : Ptd i} (f : fst (X ∙→ Y)) → Path
  {A = Σ _ (λ {(U , V , W) → fst (U ∙→ V) × fst (V ∙→ W)})}
  (_ , ptd-susp-fmap f , ptd-cfcod (ptd-susp-fmap f))
  (_ , ptd-susp-fmap f , ptd-susp-fmap (ptd-cfcod f))
suspend-cofiber f =
  ap (λ {((U , V , W) , _ , g , _) → ((U , V , Ptd-Cof g) , g , ptd-cfcod g)})
     (! (cofiber-sequence f))
  ∙ ap (λ {(_ , _ , g , h) → (_ , g , h)}) (cofiber-sequence f)

suspend^-cof= : {X Y Z : Ptd i} (m : ℕ) (f : fst (X ∙→ Y)) (g : fst (Y ∙→ Z))
  (p : Path {A = Σ _ (λ U → fst (Y ∙→ U))} (Ptd-Cof f , ptd-cfcod f) (Z , g))
  → Path {A = Σ _ (λ {(U , V , W) → fst (U ∙→ V) × fst (V ∙→ W)})}
    (_ , ptd-susp^-fmap m f , ptd-cfcod (ptd-susp^-fmap m f))
    (_ , ptd-susp^-fmap m f , ptd-susp^-fmap m g)
suspend^-cof= O f g p = ap (λ {(_ , h) → (_ , f , h)}) p
suspend^-cof= (S m) f g p =
  suspend-cofiber (ptd-susp^-fmap m f)
  ∙ ap (λ {(_ , h , k) → (_ , ptd-susp-fmap h , ptd-susp-fmap k)})
       (suspend^-cof= m f g p)
