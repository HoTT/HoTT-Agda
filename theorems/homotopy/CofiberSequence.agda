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

    ⊙into : ⊙Cofiber² f ⊙→ ⊙Susp (de⊙ X)
    ⊙into = into , ! (merid (pt X))

    module Out = SuspRec {C = de⊙ (⊙Cofiber² f)}
      (cfcod cfbase) cfbase
      (λ x → ap cfcod (cfglue x) ∙ ! (cfglue (fst f x)))

    out : Susp (de⊙ X) → Cofiber² (fst f)
    out = Out.f

    abstract
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

    ⊙eqv : ⊙Cofiber² f ⊙≃ ⊙Susp (de⊙ X)
    ⊙eqv = ≃-to-⊙≃ eqv (! (merid (pt X)))

module _ {X Y : Ptd i} (f : X ⊙→ Y) where

  ⊙Cof²-to-⊙Susp : ⊙Cofiber² f ⊙→ ⊙Susp (de⊙ X)
  ⊙Cof²-to-⊙Susp = Equiv.⊙into f

  Cof²-to-Susp = fst ⊙Cof²-to-⊙Susp

  ⊙Susp-to-⊙Cof² : ⊙Susp (de⊙ X) ⊙→ ⊙Cofiber² f
  ⊙Susp-to-⊙Cof² = ⊙<– (Equiv.⊙eqv f)

  Susp-to-Cof² = fst ⊙Susp-to-⊙Cof²

  Cof²-equiv-Susp : Cofiber² (fst f) ≃ Susp (de⊙ X)
  Cof²-equiv-Susp = Equiv.eqv f

  cod²-extract-glue-comm-sqr : CommSquare (cfcod²' (fst f)) extract-glue (idf _) Cof²-to-Susp
  cod²-extract-glue-comm-sqr  = comm-sqr λ _ → idp

  extract-glue-cod²-comm-sqr : CommSquare extract-glue (cfcod²' (fst f)) (idf _) Susp-to-Cof²
  extract-glue-cod²-comm-sqr = CommSquare-inverse-v cod²-extract-glue-comm-sqr
                                 (idf-is-equiv _) (snd Cof²-equiv-Susp)

  abstract
    cod³-Susp-fmap-comm-sqr : CommSquare (cfcod³' (fst f)) (Susp-fmap (fst f))
      Cof²-to-Susp (Susp-flip ∘ Equiv.into (⊙cfcod' f))
    cod³-Susp-fmap-comm-sqr = comm-sqr $ Cofiber-elim {f = cfcod' (fst f)}
      idp
      (Cofiber-elim {f = fst f}
        idp (λ y → merid y)
        (λ x → ↓-cst=app-in $
            ap (idp ∙'_)
              ( ap-∘ (Susp-fmap (fst f)) extract-glue (cfglue x)
              ∙ ap (ap (Susp-fmap (fst f))) (ExtractGlue.glue-β x)
              ∙ SuspFmap.merid-β (fst f) x)
          ∙ ∙'-unit-l (merid (fst f x))))
      (λ y → ↓-='-in' $
          ap (Susp-fmap (fst f) ∘ Cof²-to-Susp) (cfglue y)
            =⟨ ap-∘ (Susp-fmap (fst f)) Cof²-to-Susp (cfglue y) ⟩
          ap (Susp-fmap (fst f)) (ap Cof²-to-Susp (cfglue y))
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
            =∎)

  iterated-cofiber-seq : PtdMapSequence X (⊙Cofiber³ f)
  iterated-cofiber-seq =
    X
      ⊙→⟨ f ⟩
    Y
      ⊙→⟨ ⊙cfcod' f ⟩
    ⊙Cofiber f
      ⊙→⟨ ⊙cfcod²' f ⟩
    ⊙Cofiber² f
      ⊙→⟨ ⊙cfcod³' f ⟩
    ⊙Cofiber³ f ⊙⊣|

  cyclic-cofiber-seq : PtdMapSequence X (⊙Susp (de⊙ Y))
  cyclic-cofiber-seq =
    X
      ⊙→⟨ f ⟩
    Y
      ⊙→⟨ ⊙cfcod' f ⟩
    ⊙Cofiber f
      ⊙→⟨ ⊙extract-glue ⟩
    ⊙Susp (de⊙ X)
      ⊙→⟨ ⊙Susp-fmap (fst f) ⟩
    ⊙Susp (de⊙ Y) ⊙⊣|

  iterated-to-cyclic : PtdMapSeqMap iterated-cofiber-seq cyclic-cofiber-seq
    (⊙idf X) (⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f))
  iterated-to-cyclic =
    ⊙idf X                                  ⊙↓⟨ comm-sqr (λ _ → idp) ⟩
    ⊙idf Y                                  ⊙↓⟨ comm-sqr (λ _ → idp) ⟩
    ⊙idf (⊙Cofiber f)                       ⊙↓⟨ cod²-extract-glue-comm-sqr ⟩
    ⊙Cof²-to-⊙Susp                          ⊙↓⟨ cod³-Susp-fmap-comm-sqr ⟩
    ⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f) ⊙↓|

  iterated-to-cyclic-is-equiv : is-⊙seq-equiv iterated-to-cyclic
  iterated-to-cyclic-is-equiv =
      idf-is-equiv _
    , idf-is-equiv _
    , idf-is-equiv _
    , snd (Equiv.eqv f)
    , snd (Susp-flip-equiv ∘e (Equiv.eqv (⊙cfcod' f)))

  iterated-equiv-cyclic : PtdMapSeqEquiv iterated-cofiber-seq cyclic-cofiber-seq
    (⊙idf X) (⊙Susp-flip Y ⊙∘ Equiv.⊙into (⊙cfcod' f))
  iterated-equiv-cyclic = iterated-to-cyclic , iterated-to-cyclic-is-equiv
