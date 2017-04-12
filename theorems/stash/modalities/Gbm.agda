{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities

module stash.modalities.Gbm {ℓ} (M : Modality ℓ) where

open Modality M

BM-Relation : {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ) → Type ℓ
BM-Relation {A} {B} Q =
  {a₀ : A} {b₀ : B} (q₀ : Q a₀ b₀)
  {a₁ : A} (q₁ : Q a₁ b₀)
  {b₁ : B} (q₂ : Q a₀ b₁) → 
  is-◯-connected (((a₀ , q₀) == (a₁ , q₁)) * ((b₀ , q₀) == (b₁ , q₂)))

module _ {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ)
         (H : BM-Relation Q) where

  open import stash.modalities.gbm.Pushout Q
  import stash.modalities.gbm.CoherenceData M Q H as Coh

  -- These extra parameters will be discharged in the end
  module _ {a₀} {b₀} (q₀₀ : Q a₀ b₀) where

    -- Step 1:
    -- Generalizing the theorem to [bmleft x == p] for arbitrary p.
    -- This requires a pushout-rec

    -- "extended" version
    code-bmleft-template : ∀ a₁ {p} (r' : bmleft a₁ == p) → bmleft a₀ == p → Type ℓ
    code-bmleft-template a₁ r' r = ◯ (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' r') r)

    code-bmleft : ∀ a₁ → bmleft a₀ == bmleft a₁ → Type ℓ
    code-bmleft a₁ = code-bmleft-template a₁ idp

    code-bmright : ∀ b₁ → bmleft a₀ == bmright b₁ → Type ℓ
    code-bmright b₁ r = ◯ (hfiber bmglue r)

    -- The template from [Coh.eqv] to the input for [apd code glue]
    -- for using the identification elimination.
    code-bmglue-template : ∀ {a₁ p}
      → (code : (r : bmleft a₀ == p) → Type ℓ)
      → (r : bmleft a₁ == p)
      → (∀ r' → code-bmleft-template a₁ r r' ≃ code r')
      → code-bmleft-template a₁ idp == code [ (λ p → bmleft a₀ == p → Type ℓ) ↓ r ]
    code-bmglue-template _ idp lemma = λ= (ua ∘ lemma)

    -- The real glue, that is, the template with actual equivalence.
    code-bmglue : ∀ {a₁ b₁} (q₁₁ : Q a₁ b₁)
      → code-bmleft a₁ == code-bmright b₁
        [ (λ p → bmleft a₀ == p → Type ℓ) ↓ bmglue q₁₁ ]
    code-bmglue {a₁} {b₁} q₁₁ =
      code-bmglue-template (code-bmright b₁) (bmglue q₁₁) (Coh.eqv q₀₀ q₁₁)

    -- Here's the data structure for the generalized theorem.
    module Code = BMPushoutElim code-bmleft code-bmright code-bmglue

    code : ∀ p → bmleft a₀ == p → Type ℓ
    code = Code.f

    -- Step 2:
    -- [code] is contractible!

    -- The center for [idp].  We will use transport to find the center
    -- in other fibers.
    code-center-idp : code (bmleft a₀) idp
    code-center-idp = η (q₀₀ , !-inv'-r (bmglue q₀₀))

    -- The following is the breakdown of the path for coercing:
    --   [ap2 code r (↓-cst=idf-in' r)]
    -- We will need the broken-down version anyway,
    -- so why not breaking them down from the very beginning?

    -- The template here, again, is to keep the possibility
    -- of plugging in [idp] for [r].
    coerce-path-template : ∀ {p} r
      → code-bmleft a₀ == code p [ (λ p → bmleft a₀ == p → Type ℓ) ↓ r ]
      → code-bmleft a₀ idp == code p r
    coerce-path-template idp lemma = app= lemma idp

    -- The real path.
    coerce-path : ∀ {p} r → code (bmleft a₀) idp == code p r
    coerce-path r = coerce-path-template r (apd code r)

    -- Find the center in other fibers.
    code-center : ∀ {p} r → code p r
    code-center r = coe (coerce-path r) code-center-idp

    -- Part of the decomposed [coe (coerce-path r)]
    code-bmleft-template-diag : ∀ {p} (r : bmleft a₀ == p)
      → code-bmleft a₀ idp → code-bmleft-template a₀ r r
    code-bmleft-template-diag r = ◯-rec ◯-is-local
      λ {(q₀₀' , shift) →
        η (q₀₀' , ! (∙'-assoc (bmglue q₀₀) (! (bmglue q₀₀')) r) ∙ ap (_∙' r) shift ∙' ∙'-unit-l r )}

    abstract
      code-bmleft-template-diag-idp : ∀ x → code-bmleft-template-diag idp x == x
      code-bmleft-template-diag-idp = ◯-elim (λ _ → =-preserves-local ◯-is-local)
        (λ{(q₁₀ , shift) → {!ap (λ p → η (q₁₀ , p)) (ap-idf shift)!} })
        -- Trunc-elim (λ _ → =-preserves-level Trunc-level)
        --   λ{(q₁₀ , shift) → ap (λ p → [ q₁₀ , p ]) (ap-idf shift)}

    -- Here shows the use of two templates.  It will be super painful
    -- if we cannot throw in [idp].  Now we only have to deal with
    -- simple computations.
    abstract
      coe-coerce-path-code-bmglue-template : ∀ {p} (r : bmleft a₀ == p)
        (lemma : ∀ r' → code-bmleft-template a₀ r r' ≃ code p r')
        (x : code-bmleft a₀ idp)
        → coe (coerce-path-template r (code-bmglue-template (code p) r lemma)) x
        == –> (lemma r) (code-bmleft-template-diag r x)
      coe-coerce-path-code-bmglue-template idp lemma x =
        coe (app= (λ= (ua ∘ lemma)) idp) x
          =⟨ ap (λ p → coe p x) (app=-β (ua ∘ lemma) idp) ⟩
        coe (ua (lemma idp)) x
          =⟨ coe-β (lemma idp) x ⟩
        –> (lemma idp) x
          =⟨ ! (ap (–> (lemma idp)) (code-bmleft-template-diag-idp x)) ⟩
        –> (lemma idp) (code-bmleft-template-diag idp x)
          =∎

    -- Here is the actually lemma we want!
    -- A succinct breakdown of [coerce-path code (glue q)].
    abstract
      coe-coerce-path-code-bmglue : ∀ {b₁} (q₀₁ : Q a₀ b₁) x
        → coe (coerce-path (bmglue q₀₁)) x
        == Coh.to q₀₀ q₀₁ (bmglue q₀₁) (code-bmleft-template-diag (bmglue q₀₁) x)
      coe-coerce-path-code-bmglue q₀₁ x = {!!}
        -- coe (coerce-path-template (bmglue q₀₁) (apd code (bmglue q₀₁))) x
        --   =⟨ ap (λ p → coe (coerce-path-template (bmglue q₀₁) p) x) (Code.glue-β q₀₁) ⟩
        -- coe (coerce-path-template (bmglue q₀₁) (code-bmglue q₀₁)) x
        --   =⟨ coe-coerce-path-code-bmglue-template (bmglue q₀₁) (Coh.eqv q₀₀ q₀₁) x ⟩
        -- Coh.to q₀₀ q₀₁ (bmglue q₀₁) (code-bmleft-template-diag (bmglue q₀₁) x)
        --   =∎

    -- This is the only case you care for contractibiltiy.
    abstract
      code-coh-lemma : ∀ {b₁} (q₀₁ : Q a₀ b₁) → code-center (bmglue q₀₁) == η (q₀₁ , idp)
      code-coh-lemma q₀₁ = {!!}
        -- coe (coerce-path (bmglue q₀₁)) code-center-idp
        --   =⟨ coe-coerce-path-code-bmglue q₀₁ code-center-idp ⟩
        -- Coh.to' q₀₀ q₀₁ (bmglue q₀₁) (q₀₀ , α₁α₁⁻¹α₂=α₂ (bmglue q₀₀) (bmglue q₀₁))
        --   =⟨ ap (Coh.To.ext q₀₀ (_ , q₀₀) (_ , q₀₁) (bmglue q₀₁)) (path-lemma (bmglue q₀₀) (bmglue q₀₁)) ⟩
        -- Coh.To.ext q₀₀ (_ , q₀₀) (_ , q₀₁) (bmglue q₀₁) (! path)
        --   =⟨ Coh.To.β-r q₀₀ (_ , q₀₁) (bmglue q₀₁) (! path) ⟩
        -- [ q₀₁ , path ∙' ! path ]
        --   =⟨ ap (λ p → [ q₀₁ , p ]) (!-inv'-r path) ⟩
        -- [ q₀₁ , idp ]
        --   =∎
        -- where
        --   path = Coh.βPair.path (Coh.βpair-bmright q₀₀ q₀₁ (bmglue q₀₁))

        --   -- this is defined to be the path generated by [code-bmleft-template-diag]
        --   α₁α₁⁻¹α₂=α₂ : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₁ == p₃)
        --     → α₁ ∙' ! α₁ ∙' α₂ == α₂
        --   α₁α₁⁻¹α₂=α₂ α₁ α₂ = ! (∙'-assoc α₁ (! α₁) α₂) ∙ ap (_∙' α₂) (!-inv'-r α₁) ∙' ∙'-unit-l α₂

        --   -- the relation of this path and the one from CoherenceData
        --   path-lemma : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₁ == p₃)
        --     → α₁α₁⁻¹α₂=α₂ α₁ α₂ == ! (Coh.α₁=α₂α₂⁻¹α₁ α₂ α₁)
        --   path-lemma idp idp = idp

    -- Make [r] free to apply identification elimination.
    code-coh : ∀ {b₁} (r : bmleft a₀ == bmright b₁) (s : hfiber bmglue r) → code-center r == η s 
    code-coh ._ (q₀₁ , idp) = code-coh-lemma q₀₁

    -- Finish the lemma.
    code-contr : ∀ {b₁} (r : bmleft a₀ == bmright b₁) → is-contr (◯ (hfiber bmglue r))
    code-contr r = code-center r , ◯-elim (λ _ → =-preserves-local ◯-is-local) (code-coh r)

module _ {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ)
         (H : BM-Relation Q) where

  import stash.modalities.gbm.Pushout
  open import stash.modalities.gbm.PushoutMono
  open import stash.modalities.gbm.PullbackSplit
  open import stash.modalities.gbm.GbmUtil
  open import homotopy.PushoutSplit

  private
  
    A' : Type ℓ
    A' = Σ A (λ a → Trunc (S ⟨-2⟩) (Σ B (λ b → Q a b)))

    Q' : A' → B → Type ℓ
    Q' (a , _) b = Q a b
  
    Q'-pth-ovr-lemma : {a₀ a₁ : A'} {b : B} (q₀ : Q' a₀ b) (q₁ : Q' a₁ b) (p : a₀ == a₁)
                 → (q₀ == q₁ [ (λ a → Q' a b) ↓ p ]) ≃ (q₀ == q₁ [ (λ a → Q a b) ↓ fst= p ])
    Q'-pth-ovr-lemma q₀ q₁ idp = ide (q₀ == q₁)                 

    Q'-is-BM-Relation : BM-Relation Q'
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

    postulate
      Z≃Z' : is-equiv Z-to-Z'

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
    V≃A'-coh : (v : V) → Pullback.b v == left (fst V≃A' v)
    V≃A'-coh (pullback a b h) = {!(fst V-equiv-A' (pullback a b h))!}

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
            (λ{(_ , q₀₀) → code-contr Q' Q'-is-BM-Relation q₀₀ r}) (snd a')))

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

  generalized-blakers-massey : is-◯-equiv bm-map
  generalized-blakers-massey pb = equiv-preserves-◯-conn (lemma ⁻¹) (bm-map'-is-◯-equiv (fst Pb≃Pb' pb))

    where lemma : hfiber bm-map pb ≃ hfiber bm-map' (fst Pb≃Pb' pb)
          lemma = map-equiv-hfiber bm-map bm-map' Z-to-Z' (fst Pb≃Pb') {!!} Z≃Z' (snd Pb≃Pb') pb
          
