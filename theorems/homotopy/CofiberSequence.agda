{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.PtdMapSequence

module homotopy.CofiberSequence {i} where

{- Useful abbreviations -}
module _ {X Y : Ptd i} (f : X ⊙→ Y) where

  ⊙Cofiber² = ⊙Cofiber (⊙cfcod' f)
  ⊙cfcod²' = ⊙cfcod' (⊙cfcod' f)

  ⊙Cofiber³ = ⊙Cofiber ⊙cfcod²'
  ⊙cfcod³' = ⊙cfcod' ⊙cfcod²'

module _ {A B : Type i} (f : A → B) where

  Cofiber² = Cofiber (cfcod' f)
  cfcod²' = cfcod' (cfcod' f)

  Cofiber³ = Cofiber cfcod²'
  cfcod³' = cfcod' cfcod²'

{- For [f : X → Y], the cofiber space [Cofiber(cfcod f)] is equivalent to
 - [Susp X]. This is essentially an application of the two pushouts
 - lemma:
 -
 -       f
 -   X ––––> Y ––––––––––––––> ∙
 -   |       |                 |
 -   |       |cfcod f          |
 -   v       v                 v
 -   ∙ ––> Cofiber f ––––––––––> Cofiber² f
 -                cfcod² f
 -
 - The map [cfcod² f : Cofiber f → Cofiber² f] becomes [extract-glue : Cofiber f → ΣX],
 - and the map [cfcod³ f : Cofiber² f → Cofiber³ f] becomes [Susp-fmap f : ΣX → ΣY].
 -}
private
  {- the equivalences between [Cofiber² f] and [ΣX] (and so [Cofiber³ f] and [ΣY]) -}
  module Equiv {X Y : Ptd i} (f : X ⊙→ Y) where

    module Into = CofiberRec {f = cfcod' (fst f)} {C = Susp (de⊙ X)}
      south extract-glue (λ _ → idp)

    into : Cofiber² (fst f) → Susp (de⊙ X)
    into = Into.f

    ⊙into : ⊙Cofiber² f ⊙→ ⊙Susp X
    ⊙into = into , ! (merid (pt X))

    module Out = SuspRec {C = de⊙ (⊙Cofiber² f)}
      (cfcod cfbase) cfbase
      (λ x → ap cfcod (cfglue x) ∙ ! (cfglue (fst f x)))

    out : Susp (de⊙ X) → Cofiber² (fst f)
    out = Out.f

    into-out : ∀ σ → into (out σ) == σ
    into-out = Susp-elim idp idp
      (λ x → ↓-∘=idf-in' into out $
        ap (ap into) (Out.merid-β x)
        ∙ ap-∙ into (ap cfcod (cfglue x)) (! (cfglue (fst f x)))
        ∙ ap (λ w → ap into (ap cfcod (cfglue x)) ∙ w)
             (ap-! into (cfglue (fst f x)) ∙ ap ! (Into.glue-β (fst f x)))
        ∙ ∙-unit-r _
        ∙ ∘-ap into cfcod (cfglue x) ∙ ExtractGlue.glue-β x)

    out-into : ∀ κ → out (into κ) == κ
    out-into = Cofiber-elim {f = cfcod' (fst f)}
      idp
      (Cofiber-elim {f = fst f} idp cfglue
        (λ x → ↓-='-from-square $
          (ap-∘ out extract-glue (cfglue x)
           ∙ ap (ap out) (ExtractGlue.glue-β x) ∙ Out.merid-β x)
          ∙v⊡ (vid-square {p = ap cfcod (cfglue x)}
               ⊡h rt-square (cfglue (fst f x)))
          ⊡v∙ ∙-unit-r _))
      (λ y → ↓-∘=idf-from-square out into $
         ap (ap out) (Into.glue-β y) ∙v⊡ connection)

    eqv : Cofiber² (fst f) ≃ Susp (de⊙ X)
    eqv = equiv into out into-out out-into

    ⊙eqv : ⊙Cofiber² f ⊙≃ ⊙Susp X
    ⊙eqv = ≃-to-⊙≃ eqv (! (merid (pt X)))

module _ {X Y : Ptd i} (f : X ⊙→ Y) where

  private
    square₁ : CommSquare (cfcod²' (fst f)) extract-glue (idf _) (Equiv.into f)
    square₁ = record {commutes = λ _ → idp}

    square₂ : CommSquare (cfcod³' (fst f)) (Susp-fmap (fst f))
      (Equiv.into f) (Susp-flip ∘ Equiv.into (⊙cfcod' f))
    square₂ = record {
      commutes = Cofiber-elim {f = cfcod' (fst f)}
        idp
        (Cofiber-elim {f = fst f}
          idp (λ y → merid y)
          (λ x → ↓-cst=app-in $
              ap (idp ∙'_)
                ( ap-∘ (Susp-fmap (fst f)) extract-glue (cfglue x)
                ∙ ap (ap (Susp-fmap (fst f))) (ExtractGlue.glue-β x)
                ∙ SuspFmap.merid-β (fst f) x)
            ∙ ∙'-unit-l (merid (fst f x))))
        (λ y → ↓-='-in' (
            ap (Susp-fmap (fst f) ∘ Equiv.into f) (cfglue y)
              =⟨ ap-∘ (Susp-fmap (fst f)) (Equiv.into f) (cfglue y) ⟩
            ap (Susp-fmap (fst f)) (ap (Equiv.into f) (cfglue y))
              =⟨ Equiv.Into.glue-β f y |in-ctx ap (Susp-fmap (fst f)) ⟩
            idp
              =⟨ ! $ !-inv'-l (merid y) ⟩
            ! (merid y) ∙' merid y
              =⟨ ! $ SuspFlip.merid-β y |in-ctx _∙' merid y ⟩
            ap Susp-flip (merid y) ∙' merid y
              =⟨ ! $ ExtractGlue.glue-β y |in-ctx (λ p → ap Susp-flip p ∙' merid y) ⟩
            ap Susp-flip (ap extract-glue (cfglue y)) ∙' merid y
              =⟨ ! $ ap-∘ Susp-flip extract-glue (cfglue y) |in-ctx _∙' merid y ⟩
            ap (Susp-flip ∘ extract-glue) (cfglue y) ∙' merid y
              =∎))}

  Cofiber²-equiv-Susp-dom : Cofiber² (fst f) ≃ Susp (de⊙ X)
  Cofiber²-equiv-Susp-dom = Equiv.eqv f

  ⊙Cofiber²-equiv-⊙Susp-dom : ⊙Cofiber² f ⊙≃ ⊙Susp X
  ⊙Cofiber²-equiv-⊙Susp-dom = Equiv.⊙eqv f

  iterated-cofiber-seq : PtdMapSequence X (⊙Cofiber³ f)
  iterated-cofiber-seq =
    X ⊙→⟨ f ⟩ Y ⊙→⟨ ⊙cfcod' f ⟩ ⊙Cofiber f ⊙→⟨ ⊙cfcod²' f ⟩ ⊙Cofiber² f ⊙→⟨ ⊙cfcod³' f ⟩ ⊙Cofiber³ f ⊙⊣|

  cofiber-seq : PtdMapSequence X (⊙Susp Y)
  cofiber-seq =
    X ⊙→⟨ f ⟩ Y ⊙→⟨ ⊙cfcod' f ⟩ ⊙Cofiber f ⊙→⟨ ⊙extract-glue ⟩ ⊙Susp X ⊙→⟨ ⊙Susp-fmap f ⟩ ⊙Susp Y ⊙⊣|

  cofiber-seq-map : PtdMapSeqMap iterated-cofiber-seq cofiber-seq
    (⊙idf X) (⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f))
  cofiber-seq-map =
    ⊙idf X                                  ⊙↓⟨ comm-sqr (λ _ → idp) ⟩
    ⊙idf Y                                  ⊙↓⟨ comm-sqr (λ _ → idp) ⟩
    ⊙idf (⊙Cofiber f)                       ⊙↓⟨ square₁ ⟩
    Equiv.⊙into f                           ⊙↓⟨ square₂ ⟩
    ⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f) ⊙↓|

  cofiber-seq-map-is-equiv : is-⊙seq-equiv cofiber-seq-map
  cofiber-seq-map-is-equiv =
      idf-is-equiv _
    , idf-is-equiv _
    , idf-is-equiv _
    , snd (Equiv.eqv f)
    , snd (Susp-flip-equiv ∘e (Equiv.eqv (⊙cfcod' f)))

  cofiber-seq-equiv : PtdMapSeqEquiv iterated-cofiber-seq cofiber-seq
    (⊙idf X) (⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f))
  cofiber-seq-equiv = cofiber-seq-map , cofiber-seq-map-is-equiv
