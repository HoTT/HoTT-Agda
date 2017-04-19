{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
open import stash.modalities.gbm.GbmUtil
open import stash.modalities.GbmCodes

module stash.modalities.Gbm {ℓ} (M : Modality ℓ) 
  {A : Type ℓ} {B : Type ℓ}
  (Q : A → B → Type ℓ)
  (H : BM-Relation M Q) where

  open Modality M
  
  import stash.modalities.gbm.Pushout
  open import stash.modalities.gbm.PushoutMono
  open import stash.modalities.gbm.PullbackSplit
  open import homotopy.PushoutSplit

  private
  
    A' : Type ℓ
    A' = Σ A (λ a → Trunc (S ⟨-2⟩) (Σ B (λ b → Q a b)))

    Q' : A' → B → Type ℓ
    Q' (a , _) b = Q a b
  
    Q'-pth-ovr-lemma : {a₀ a₁ : A'} {b : B} (q₀ : Q' a₀ b) (q₁ : Q' a₁ b) (p : a₀ == a₁)
                 → (q₀ == q₁ [ (λ a → Q' a b) ↓ p ]) ≃ (q₀ == q₁ [ (λ a → Q a b) ↓ fst= p ])
    Q'-pth-ovr-lemma q₀ q₁ idp = ide (q₀ == q₁)                 

    Q'-is-BM-Relation : BM-Relation M Q'
    Q'-is-BM-Relation {a₀} {b₀} q₀ {a₁} q₁ {b₁} q₂ =
      equiv-preserves-◯-conn (*-emap eqv (ide _))
        (H {fst a₀} {b₀} q₀ {fst a₁} q₁ {b₁} q₂)

      where eqv = =Σ-econv (a₀ , q₀) (a₁ , q₁)
                    ∘e (Σ-emap-r (Q'-pth-ovr-lemma q₀ q₁)) ⁻¹
                    ∘e (Σ-emap-l (λ p → q₀ == q₁ [ (λ a → Q a b₀) ↓ p ])
                         (Subtype=-econv ((λ a → Trunc -1 (Σ B λ b → Q a b)), λ a → Trunc-level) a₀ a₁ ⁻¹)) ⁻¹
                    ∘e (=Σ-econv (fst a₀ , q₀) (fst a₁ , q₁)) ⁻¹

    module W = stash.modalities.gbm.Pushout Q
    module W' = stash.modalities.gbm.Pushout Q'
    W  = W.BMPushout
    W' = W'.BMPushout

    Z = (Σ A λ a → Σ B λ b → Q a b)
    Z' = (Σ A' λ a → Σ B λ b → Q (fst a) b)

    Z-to-Z' : Z → Z'
    Z-to-Z' (a , b , q) = (a , [ b , q ]) , b , q

    Z'-to-Z : Z' → Z
    Z'-to-Z ((a , e) , b , q) = a , b , q

    Z≃Z' : is-equiv Z-to-Z'
    Z≃Z' = is-eq Z-to-Z' Z'-to-Z to-from from-to

      where to-from : (z : Z') → Z-to-Z' (Z'-to-Z z) == z
            to-from ((a , e) , b , q) = pair= (pair= idp (prop-has-all-paths Trunc-level _ e))
              (↓-cst2-in idp (prop-has-all-paths Trunc-level _ e) idp)

            from-to : (z : Z) → Z'-to-Z (Z-to-Z' z) == z
            from-to (a , b , q) = idp
            
    W-span = span A B Z fst (fst ∘ snd)
    W''-span = span A B Z' (fst ∘ fst) (fst ∘ snd)

    W'' = Pushout W''-span

    W≃W'' : W ≃ W''
    W≃W'' = Pushout-emap span-eqv

      where span-eqv : SpanEquiv W-span W''-span
            span-eqv = (span-map (idf A) (idf B) Z-to-Z'
                         (comm-sqr (λ a → idp))
                         (comm-sqr (λ b → idp))) ,
                         ( idf-is-equiv A
                         , idf-is-equiv B
                         , Z≃Z')

    --
    --  But the PushoutSplit lemma, we find that
    --
    --    Z' ---------> B   
    --    |             |   
    --    |             |
    --    v             v
    --    A' ---------> W'
    --    |             |
    --    |             |
    --    v             v
    --    A ----------> W'' ≃ X
    --

    X = Pushout (span A W' A' fst left)

    W''≃X : W'' ≃ X
    W''≃X = PS.split-equiv

      where module PS = PushoutLSplit {A = A'} {B = A} {C = B} {D = Z'} fst fst (fst ∘ snd)

    --
    --  Now we switch gears and take pullbacks.  We
    --  have the following diagram:
    --
    -- U'' ≃  U' ≃ U ---------> B  
    --             |            |
    --             |            |
    --             v            v
    --        A' ≃ V ---------> W'  outer = cospan₀
    --             |            |
    --             |  cospan₂   |
    --             v            v
    --             A ---------> X ≃ W''
    
    V = Pullback (cospan A W' X left right)

    U = Pullback (cospan A B X left (right ∘ W'.bmright))
    U' = Pullback (cospan A B W'' left right)
    U'' = Pullback (cospan V B W' Pullback.b right)

    U≃U'' : U ≃ U''
    U≃U'' = PBSplit.split-equiv

      where module PBSplit = PullbackLSplit {A = W'} {B = B} {C = A} {D = X} right right left

    --
    --  The map A' --> A is a mono.  Hence by
    --  the PushoutMono lemma we get that it
    --  is also a pullback and consequently 
    --  equivalent to V
    --

    V≃A' : V ≃ A'
    V≃A' = (ML.pushout-mono-is-pullback) ⁻¹ ∘e (pullback-decomp-equiv (cospan A W' X left right))

      where module ML = MonoLemma
              (span A W' A' fst left)
              (λ b → equiv-preserves-level ((hfiber-fst b) ⁻¹) Trunc-level)

    -- We need this for commutivity below
    postulate 
      V≃A'-coh : (v : V) → Pullback.b v == left (fst V≃A' v)
    -- V≃A'-coh (pullback a b h) = {!(fst V-equiv-A' (pullback a b h))!}

    --
    --  Now on to the main theorem
    --

    A×WB = Pullback (cospan A B W left right)
    A'×W'B = Pullback (cospan A' B W' left right)

    U''≃A'×W'B : U'' ≃ A'×W'B
    U''≃A'×W'B = Pullback-emap cospan-eqv

      where cospan-eqv : CospanEquiv (cospan V B W' Pullback.b right)
                                     (cospan A' B W' left right)
            cospan-eqv = (cospan-map (fst (V≃A')) (idf B) (idf W')
                                     (comm-sqr V≃A'-coh) 
                                     (comm-sqr (λ b → idp))) ,
                                     snd (V≃A') ,
                                     idf-is-equiv B ,
                                     idf-is-equiv W'


    A×WB≃U : A×WB ≃ U
    A×WB≃U = Pullback-emap cospan-eqv

      where cospan-eqv : CospanEquiv (cospan A B W left right) (cospan A B X left (right ∘ W'.bmright))
            cospan-eqv = (cospan-map (idf A) (idf B) (fst (W''≃X ∘e W≃W''))
                                     (comm-sqr (λ a → idp))
                                     (comm-sqr (λ b → idp))) ,
                                     idf-is-equiv A ,
                                     (idf-is-equiv B) ,
                                     (snd (W''≃X ∘e W≃W''))

    pullback-equiv : A×WB ≃ A'×W'B
    pullback-equiv = A×WB ≃⟨ A×WB≃U ⟩
                     U ≃⟨ U≃U'' ⟩ 
                     U'' ≃⟨ U''≃A'×W'B ⟩ 
                     A'×W'B ≃∎

    Pb = Σ A (λ a → Σ B (λ b →  W.bmleft a == W.bmright b))
    Pb' = Σ A' (λ a → Σ B (λ b →  W'.bmleft a == W'.bmright b))

    Pb≃Pb' = Pb ≃⟨ Σ-assoc ⁻¹  ⟩
             Σ (A × B) (λ ab → W.bmleft (fst ab) == W.bmright (snd ab)) ≃⟨ (pullback-decomp-equiv (cospan A B W left right)) ⁻¹  ⟩
             A×WB ≃⟨ pullback-equiv ⟩
             A'×W'B ≃⟨ pullback-decomp-equiv (cospan A' B W' left right) ⟩ 
             Σ (A' × B) (λ ab → W'.bmleft (fst ab) == W'.bmright (snd ab)) ≃⟨ Σ-assoc ⟩
             Pb' ≃∎

    bm-map : Z → Pb
    bm-map (a , b , q) = a , b , W.bmglue q
    
    bm-map' : Z' → Pb'
    bm-map' (a' , b , q) = a' , b , W'.bmglue q 

    bm-map'-is-◯-equiv : is-◯-equiv bm-map'
    bm-map'-is-◯-equiv =
      total-◯-equiv
        (λ a' → λ { (b , q) → b , W'.bmglue q})
        (λ a' → total-◯-equiv (λ b q → W'.bmglue q)
          (λ b r → Trunc-rec (prop-has-level-S is-◯-connected-is-prop)
            (λ{(_ , q₀₀) → code-contr M Q' Q'-is-BM-Relation q₀₀ r}) (snd a')))

  --
  --  We have a commutative diagram with top and bottom
  --  maps equivalences.  This induces an equivalence on
  --  homotopy fibers, from which the theorem follows
  --          ~
  --    Z --------> Z'
  --    |           |
  --  s |           | t
  --    |           |
  --    v           v
  --    Pb -------> Pb'
  --          ~
  --

  postulate
   sq-coh : (z : Z) → (fst Pb≃Pb' (bm-map z)) == bm-map' (Z-to-Z' z)
   -- sq-coh (a , b , q) = fst Pb≃Pb' (a , b , W.bmglue q) =⟨ {!!} ⟩
   --                       (a , [ b , q ]) , (b , W'.bmglue q) ∎
   
  generalized-blakers-massey : is-◯-equiv bm-map
  generalized-blakers-massey pb = equiv-preserves-◯-conn (lemma ⁻¹) (bm-map'-is-◯-equiv (fst Pb≃Pb' pb))

    where 

          lemma : hfiber bm-map pb ≃ hfiber bm-map' (fst Pb≃Pb' pb)
          lemma = hfiber-sq-eqv bm-map bm-map' Z-to-Z' (fst Pb≃Pb')
            (comm-sqr sq-coh) Z≃Z' (snd Pb≃Pb') pb

  
