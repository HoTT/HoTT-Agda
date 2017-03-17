{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (left; right)

module homotopy.BlakersMassey {i j k}
  {A : Type i} {B : Type j} (Q : A → B → Type k)
  m (f-conn : ∀ a → is-connected (S m) (Σ B (λ b → Q a b)))
  n (g-conn : ∀ b → is-connected (S n) (Σ A (λ a → Q a b)))
  where

  open import homotopy.blakersmassey.Pushout Q
  import homotopy.blakersmassey.CoherenceData Q m f-conn n g-conn as Coh

  -- These extra parameters will be discharged in the end
  module _ {a₀} {b₀} (q₀₀ : Q a₀ b₀) where

    -- Step 1:
    -- Generalizing the theorem to [bmleft x == p] for arbitrary p.
    -- This requires a pushout-rec

    -- "extended" version
    code-bmleft-template : ∀ a₁ {p} (r' : bmleft a₁ == p) → bmleft a₀ == p → Type (lmax i (lmax j k))
    code-bmleft-template a₁ r' r = Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' r') r)

    code-bmleft : ∀ a₁ → bmleft a₀ == bmleft a₁ → Type (lmax i (lmax j k))
    code-bmleft a₁ = code-bmleft-template a₁ idp

    code-bmright : ∀ b₁ → bmleft a₀ == bmright b₁ → Type (lmax i (lmax j k))
    code-bmright b₁ r = Trunc (m +2+ n) (hfiber bmglue r)

    -- The template from [Coh.eqv] to the input for [apd code glue]
    -- for using the identification elimination.
    code-bmglue-template : ∀ {a₁ p}
      → (code : (r : bmleft a₀ == p) → Type (lmax i (lmax j k)))
      → (r : bmleft a₁ == p)
      → (∀ r' → code-bmleft-template a₁ r r' ≃ code r')
      → code-bmleft-template a₁ idp == code [ (λ p → bmleft a₀ == p → Type (lmax i (lmax j k))) ↓ r ]
    code-bmglue-template _ idp lemma = λ= (ua ∘ lemma)

    -- The real glue, that is, the template with actual equivalence.
    code-bmglue : ∀ {a₁ b₁} (q₁₁ : Q a₁ b₁)
      → code-bmleft a₁ == code-bmright b₁
        [ (λ p → bmleft a₀ == p → Type (lmax i (lmax j k))) ↓ bmglue q₁₁ ]
    code-bmglue {a₁} {b₁} q₁₁ =
      code-bmglue-template (code-bmright b₁) (bmglue q₁₁) (Coh.eqv q₀₀ q₁₁)

    -- Here's the data structure for the generalized theorem.
    module Code = BMPushoutElim code-bmleft code-bmright code-bmglue

    code : ∀ p → bmleft a₀ == p → Type (lmax i (lmax j k))
    code = Code.f

    -- Step 2:
    -- [code] is contractible!

    -- The center for [idp].  We will use transport to find the center
    -- in other fibers.
    code-center-idp : code (bmleft a₀) idp
    code-center-idp = [ q₀₀ , !-inv'-r (bmglue q₀₀) ]

    -- The following is the breakdown of the path for coercing:
    --   [ap2 code r (↓-cst=idf-in' r)]
    -- We will need the broken-down version anyway,
    -- so why not breaking them down from the very beginning?

    -- The template here, again, is to keep the possibility
    -- of plugging in [idp] for [r].
    coerce-path-template : ∀ {p} r
      → code-bmleft a₀ == code p [ (λ p → bmleft a₀ == p → Type (lmax i (lmax j k))) ↓ r ]
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
    code-bmleft-template-diag r = Trunc-rec Trunc-level
      λ {(q₀₀' , shift) →
        [ q₀₀' , ! (∙'-assoc (bmglue q₀₀) (! (bmglue q₀₀')) r) ∙ ap (_∙' r) shift ∙' ∙'-unit-l r ]}

    abstract
      code-bmleft-template-diag-idp : ∀ x → code-bmleft-template-diag idp x == x
      code-bmleft-template-diag-idp =
        Trunc-elim (λ _ → =-preserves-level Trunc-level)
          λ{(q₁₀ , shift) → ap (λ p → [ q₁₀ , p ]) (ap-idf shift)}

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
      coe-coerce-path-code-bmglue q₀₁ x =
        coe (coerce-path-template (bmglue q₀₁) (apd code (bmglue q₀₁))) x
          =⟨ ap (λ p → coe (coerce-path-template (bmglue q₀₁) p) x) (Code.glue-β q₀₁) ⟩
        coe (coerce-path-template (bmglue q₀₁) (code-bmglue q₀₁)) x
          =⟨ coe-coerce-path-code-bmglue-template (bmglue q₀₁) (Coh.eqv q₀₀ q₀₁) x ⟩
        Coh.to q₀₀ q₀₁ (bmglue q₀₁) (code-bmleft-template-diag (bmglue q₀₁) x)
          =∎

    -- This is the only case you care for contractibiltiy.
    abstract
      code-coh-lemma : ∀ {b₁} (q₀₁ : Q a₀ b₁) → code-center (bmglue q₀₁) == [ q₀₁ , idp ]
      code-coh-lemma q₀₁ =
        coe (coerce-path (bmglue q₀₁)) code-center-idp
          =⟨ coe-coerce-path-code-bmglue q₀₁ code-center-idp ⟩
        Coh.to' q₀₀ q₀₁ (bmglue q₀₁) (q₀₀ , α₁α₁⁻¹α₂=α₂ (bmglue q₀₀) (bmglue q₀₁))
          =⟨ ap (Coh.To.ext q₀₀ (_ , q₀₀) (_ , q₀₁) (bmglue q₀₁)) (path-lemma (bmglue q₀₀) (bmglue q₀₁)) ⟩
        Coh.To.ext q₀₀ (_ , q₀₀) (_ , q₀₁) (bmglue q₀₁) (! path)
          =⟨ Coh.To.β-r q₀₀ (_ , q₀₁) (bmglue q₀₁) (! path) ⟩
        [ q₀₁ , path ∙' ! path ]
          =⟨ ap (λ p → [ q₀₁ , p ]) (!-inv'-r path) ⟩
        [ q₀₁ , idp ]
          =∎
        where
          path = Coh.βPair.path (Coh.βpair-bmright q₀₀ q₀₁ (bmglue q₀₁))

          -- this is defined to be the path generated by [code-bmleft-template-diag]
          α₁α₁⁻¹α₂=α₂ : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₁ == p₃)
            → α₁ ∙' ! α₁ ∙' α₂ == α₂
          α₁α₁⁻¹α₂=α₂ α₁ α₂ = ! (∙'-assoc α₁ (! α₁) α₂) ∙ ap (_∙' α₂) (!-inv'-r α₁) ∙' ∙'-unit-l α₂

          -- the relation of this path and the one from CoherenceData
          path-lemma : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₁ == p₃)
            → α₁α₁⁻¹α₂=α₂ α₁ α₂ == ! (Coh.α₁=α₂α₂⁻¹α₁ α₂ α₁)
          path-lemma idp idp = idp

    -- Make [r] free to apply identification elimination.
    code-coh : ∀ {b₁} (r : bmleft a₀ == bmright b₁) (s : hfiber bmglue r) → code-center r == [ s ]
    code-coh ._ (q₀₁ , idp) = code-coh-lemma q₀₁

    -- Finish the lemma.
    code-contr : ∀ {b₁} (r : bmleft a₀ == bmright b₁) → is-contr (Trunc (m +2+ n) (hfiber bmglue r))
    code-contr r = code-center r , Trunc-elim
      (λ _ → =-preserves-level Trunc-level) (code-coh r)

  -- The final theorem.
  -- It is sufficient to find some [q₀₀].
  blakers-massey : ∀ {a₀ b₀} → has-conn-fibers (m +2+ n) (bmglue {a₀} {b₀})
  blakers-massey {a₀} r = Trunc-rec
    (prop-has-level-S is-connected-is-prop)
    (λ{(_ , q₀₀) → code-contr q₀₀ r})
    (fst (f-conn a₀))
