{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (left; right)
open import stash.modalities.Modalities
-- import homotopy.WedgeExtension as WedgeExt

module stash.modalities.gbm.CoherenceData {ℓ} (M : Modality {ℓ})
  {A : Type ℓ} {B : Type ℓ} (Q : A → B → Type ℓ)
  (H : {a₀ : A} {b₀ : B}
       (α : Σ A (λ a → Q a b₀))
       (β : Σ B (λ b → Q a₀ b)) →
       is-◯-connected M (α == α) * (β == β))
  where       

open Modality M  
open import stash.modalities.gbm.Pushout Q

-- {- goal :
--     ◯ (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r)
--   ≃ ◯ (hfiber bmglue r)
-- -}

α₁=α₁α₂⁻¹α₂ : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₃ == p₂)
  → α₁ == α₁ ∙' ! α₂ ∙' α₂
α₁=α₁α₂⁻¹α₂ _ idp = idp

α₁=α₂α₂⁻¹α₁ : ∀ {p₁ p₂ p₃ : BMPushout} (α₁ : p₁ == p₂) (α₂ : p₁ == p₃)
  → α₁ == α₂ ∙' ! α₂ ∙' α₁
α₁=α₂α₂⁻¹α₁ idp α₂ = ! (!-inv'-r α₂)

private
  path-lemma₁ : ∀ {a₀ a₁ b} (q₀ : Q a₀ b) (q₁ : Q a₁ b)
    → bmglue q₀ == bmglue q₀ ∙' ! (bmglue q₁) ∙' bmglue q₁
  path-lemma₁ q₀ q₁ = α₁=α₁α₂⁻¹α₂ (bmglue q₀) (bmglue q₁)

  path-lemma₂ : ∀ {a b₀ b₁} (q₀ : Q a b₀) (q₁ : Q a b₁)
    → bmglue q₀ == bmglue q₁ ∙' ! (bmglue q₁) ∙' bmglue q₀
  path-lemma₂ q₀ q₁ = α₁=α₂α₂⁻¹α₁ (bmglue q₀) (bmglue q₁)

  abstract
    path-coherence : ∀ {a b} (q : Q a b)
      → path-lemma₁ q q == path-lemma₂ q q
    path-coherence q = lemma (bmglue q) where
      lemma : ∀ {p₀ p₁ : BMPushout} (path : p₀ == p₁)
        → α₁=α₁α₂⁻¹α₂ path path == α₁=α₂α₂⁻¹α₁ path path
      lemma idp = idp

module To {a₁ b₀} (q₁₀ : Q a₁ b₀) where
  U = Σ A λ a → Q a b₀
  u₀ : U
  u₀ = (a₁ , q₁₀)

  V = Σ B λ b → Q a₁ b
  v₀ : V
  v₀ = (b₀ , q₁₀)

  P : U → V → Type ℓ
  P u v = (r : bmleft (fst u) == bmright (fst v))
    → bmglue (snd u) ∙' ! (bmglue q₁₀) ∙' bmglue (snd v) == r
    → ◯ (hfiber bmglue r)

  template : ∀ (u : U) (v : V)
    → (r : bmleft (fst u) == bmright (fst v))
    → (shift : bmglue (snd u) ∙' ! (bmglue q₁₀) ∙' bmglue (snd v) == r)
    → ∀ q₀₁ → bmglue q₀₁ == bmglue (snd u) ∙' ! (bmglue q₁₀) ∙' bmglue (snd v)
    → ◯ (hfiber bmglue r)
  template u v r shift q₀₁ path = η (q₀₁ , path ∙' shift)

  f = λ u r shift → template u v₀ r shift (snd u) (path-lemma₁ (snd u) q₁₀)
  g = λ v r shift → template u₀ v r shift (snd v) (path-lemma₂ (snd v) q₁₀)
  p' = λ r shift → ap (template u₀ v₀ r shift q₁₀) (path-coherence q₁₀)
  p = λ= λ r → λ= λ shift → p' r shift

--   args : WedgeExt.args {A = U} {a₀ = u₀} {B = V} {b₀ = v₀}
--   args = record {
--     n = n; m = m;
--     cA = g-conn b₀;
--     cB = f-conn a₁;
--     P = λ u v → swap-level $ P u v , Π-level λ _ → Π-level λ _ → Trunc-level;
--     f = f; g = g; p = p}

--   ext : ∀ u v → P u v
--   ext = WedgeExt.ext args

--   β-l : ∀ u r shift → ext u v₀ r shift == f u r shift
--   β-l u r shift = app= (app= (WedgeExt.β-l u) r) shift

--   β-r : ∀ v r shift → ext u₀ v r shift == g v r shift
--   β-r v r shift = app= (app= (WedgeExt.β-r v) r) shift

--   abstract
--     coh : ∀ r shift → ! (β-l u₀ r shift) ∙ β-r v₀ r shift == p' r shift
--     coh r shift =
--       ! (β-l u₀ r shift) ∙ β-r v₀ r shift
--         =⟨ ap (_∙ β-r v₀ r shift) (!-ap (_$ shift) (app= (WedgeExt.β-l u₀) r))
--          ∙ ∙-ap (_$ shift)
--              (! (app= (WedgeExt.β-l {r = args} u₀) r))
--              (app= (WedgeExt.β-r {r = args} v₀) r)
--          ∙ ap (λ p → app= p shift)
--              ( ap (_∙ app= (WedgeExt.β-r {r = args} v₀) r)
--                 (!-ap (_$ r) (WedgeExt.β-l {r = args} u₀))
--              ∙ ∙-ap (_$ r)
--                 (! (WedgeExt.β-l {r = args} u₀))
--                 (WedgeExt.β-r {r = args} v₀)) ⟩
--       app= (app= (! (WedgeExt.β-l {r = args} u₀) ∙ WedgeExt.β-r {r = args} v₀) r) shift
--         =⟨ ap (λ p → app= (app= p r) shift) (WedgeExt.coh {r = args}) ⟩
--       app= (app= (λ= λ r → λ= λ shift → p' r shift) r) shift
--         =⟨ ap (λ p → app= p shift) (app=-β (λ r → λ= λ shift → p' r shift) r)
--          ∙ app=-β (λ shift → p' r shift) shift ⟩
--       p' r shift
--         =∎

-- to' : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁)
--   → (r : bmleft a₀ == bmright b₁)
--   → hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r
--   → Trunc (m +2+ n) (hfiber bmglue r)
-- to' q₀₀ q₁₁ r (q₁₀ , shift) = To.ext q₁₀ (_ , q₀₀) (_ , q₁₁) r shift

-- to : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁)
--   → (r : bmleft a₀ == bmright b₁)
--   → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r)
--   → Trunc (m +2+ n) (hfiber bmglue r)
-- to q₀₀ q₁₁ r = Trunc-rec Trunc-level (to' q₀₀ q₁₁ r)

-- module From {a₀ b₁} (q₀₁ : Q a₀ b₁) where
--   U = Σ A λ a → Q a b₁
--   u₀ : U
--   u₀ = (a₀ , q₀₁)

--   V = Σ B λ b → Q a₀ b
--   v₀ : V
--   v₀ = (b₁ , q₀₁)

--   P : U → V → Type (lmax i (lmax j k))
--   P u v = (r : bmleft a₀ == bmright b₁)
--     → bmglue q₀₁ == r
--     → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue (snd v) ∙' ! (bmglue q₁₀) ∙' bmglue (snd u)) r)

--   template : ∀ (u : U) (v : V)
--     → (r : bmleft a₀ == bmright b₁)
--     → (shift : bmglue q₀₁ == r)
--     → ∀ q₁₀ → bmglue q₀₁ == bmglue (snd v) ∙' ! (bmglue q₁₀) ∙' bmglue (snd u)
--     → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue (snd v) ∙' ! (bmglue q₁₀) ∙' bmglue (snd u)) r)
--   template u v r shift q₁₀ path = [ q₁₀ , ! path ∙' shift ]

--   f = λ u r shift → template u v₀ r shift (snd u) (path-lemma₁ q₀₁ (snd u))
--   g = λ v r shift → template u₀ v r shift (snd v) (path-lemma₂ q₀₁ (snd v))
--   p' = λ r shift → ap (template u₀ v₀ r shift q₀₁) (path-coherence q₀₁)
--   p = λ= λ r → λ= λ shift → p' r shift

--   args : WedgeExt.args {A = U} {a₀ = u₀} {B = V} {b₀ = v₀}
--   args = record {
--     n = n; m = m;
--     cA = g-conn b₁;
--     cB = f-conn a₀;
--     P = λ u v → swap-level $ P u v , Π-level λ _ → Π-level λ _ → Trunc-level;
--     f = f; g = g; p = p}

--   ext : ∀ u v → P u v
--   ext = WedgeExt.ext args

--   β-l : ∀ u r shift → ext u v₀ r shift == f u r shift
--   β-l u r shift = app= (app= (WedgeExt.β-l u) r) shift

--   β-r : ∀ v r shift → ext u₀ v r shift == g v r shift
--   β-r v r shift = app= (app= (WedgeExt.β-r v) r) shift

--   abstract
--     coh : ∀ r shift → ! (β-l u₀ r shift) ∙ β-r v₀ r shift == p' r shift
--     coh r shift =
--       ! (β-l u₀ r shift) ∙ β-r v₀ r shift
--         =⟨ ap (_∙ β-r v₀ r shift) (!-ap (_$ shift) (app= β-l' r))
--          ∙ ∙-ap (_$ shift) (! (app= β-l' r)) (app= β-r' r)
--          ∙ ap (λ p → app= p shift)
--              ( ap (_∙ app= β-r' r) (!-ap (_$ r) β-l')
--              ∙ ∙-ap (_$ r) (! β-l') β-r') ⟩
--       app= (app= (! β-l' ∙ β-r') r) shift
--         =⟨ ap (λ p → app= (app= p r) shift) (WedgeExt.coh {r = args}) ⟩
--       app= (app= (λ= λ r → λ= λ shift → p' r shift) r) shift
--         =⟨ ap (λ p → app= p shift) (app=-β (λ r → λ= λ shift → p' r shift) r)
--          ∙ app=-β (λ shift → p' r shift) shift ⟩
--       p' r shift
--         =∎
--       where β-l' = WedgeExt.β-l {r = args} u₀
--             β-r' = WedgeExt.β-r {r = args} v₀

-- from' : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁)
--   → (r : bmleft a₀ == bmright b₁)
--   → hfiber bmglue r
--   → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r)
-- from' q₀₀ q₁₁ r (q₀₁ , shift) = From.ext q₀₁ (_ , q₁₁) (_ , q₀₀) r shift

-- from : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁)
--   → (r : bmleft a₀ == bmright b₁)
--   → Trunc (m +2+ n) (hfiber bmglue r)
--   → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r)
-- from q₀₀ q₁₁ r = Trunc-rec Trunc-level (from' q₀₀ q₁₁ r)

-- -- Equivalence

-- {-
--     First step:  Pack relevant rules into records.
-- -}

-- record βPair {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀)
--   (q₁₁ : Q a₁ b₁) (q₀₁ : Q a₀ b₁) (q₁₀ : Q a₁ b₀)
--   (r : bmleft a₀ == bmright b₁) : Type (lmax i (lmax j k)) where
--   constructor βpair
--   field
--     path : bmglue q₀₁ == bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁
--     to-β : ∀ shift → To.ext q₁₀ (_ , q₀₀) (_ , q₁₁) r shift
--                   == To.template q₁₀ (_ , q₀₀) (_ , q₁₁) r shift q₀₁ path
--     from-β : ∀ shift → From.ext q₀₁ (_ , q₁₁) (_ , q₀₀) r shift
--                     == From.template q₀₁ (_ , q₁₁) (_ , q₀₀) r shift q₁₀ path

-- βpair-bmleft : ∀ {a₀ a₁ b} (q₀ : Q a₀ b) (q₁ : Q a₁ b) r
--   → βPair q₀ q₁ q₀ q₁ r
-- βpair-bmleft q₀ q₁ r = record
--   { path = path-lemma₁ q₀ q₁
--   ; to-β = To.β-l q₁ (_ , q₀) r
--   ; from-β = From.β-l q₀ (_ , q₁) r
--   }

-- βpair-bmright : ∀ {a b₀ b₁} (q₀ : Q a b₀) (q₁ : Q a b₁) r
--   → βPair q₀ q₁ q₁ q₀ r
-- βpair-bmright q₀ q₁ r = record
--   { path = path-lemma₂ q₁ q₀
--   ; to-β = To.β-r q₀ (_ , q₁) r
--   ; from-β = From.β-r q₁ (_ , q₀) r
--   }

-- abstract
--   βpair= : ∀ {a₀ a₁} {b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁)
--     (q₀₁ : Q a₀ b₁) (q₁₀ : Q a₁ b₀) (r : bmleft a₀ == bmright b₁)
--     {p₁ p₂ : bmglue q₀₁ == bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁} (p= : p₁ == p₂)
--     {toβ₁} {toβ₂}
--     (toβ= : ∀ shift → toβ₁ shift ∙ ap (To.template q₁₀ (_ , q₀₀) (_ , q₁₁) r shift q₀₁) p=
--                    == toβ₂ shift)
--     {fromβ₁} {fromβ₂}
--     (fromβ= : ∀ shift → fromβ₁ shift ∙ ap (From.template q₀₁ (_ , q₁₁) (_ , q₀₀) r shift q₁₀) p=
--                      == fromβ₂ shift)
--     → βpair p₁ toβ₁ fromβ₁ == βpair p₂ toβ₂ fromβ₂
--   βpair= q₀₀ q₁₁ q₀₁ q₁₀ r {p} idp toβ= fromβ= = lemma
--     (λ= λ shift → ! (∙-unit-r _) ∙ toβ= shift)
--     (λ= λ shift → ! (∙-unit-r _) ∙ fromβ= shift)
--     where
--       lemma : ∀ {toβ₁} {toβ₂} (toβ= : toβ₁ == toβ₂) {fromβ₁} {fromβ₂} (fromβ= : fromβ₁ == fromβ₂)
--         → βpair p toβ₁ fromβ₁ == βpair p toβ₂ fromβ₂
--       lemma idp idp = idp

-- abstract
--   βpair-glue : ∀ {a} {b} (q : Q a b) r
--     → βpair-bmleft q q r == βpair-bmright q q r
--   βpair-glue q r = βpair= q q q q r
--     (path-coherence q)
--     (λ shift →
--       To.β-l q (_ , q) r shift ∙ To.p' q r shift
--           =⟨ ! $ ap (To.β-l q (_ , q) r shift ∙_) (To.coh q r shift) ⟩
--       To.β-l q (_ , q) r shift ∙ ! (To.β-l q (_ , q) r shift) ∙ To.β-r q (_ , q) r shift
--           =⟨ ! (∙-assoc (To.β-l q (_ , q) r shift) (! (To.β-l q (_ , q) r shift)) (To.β-r q (_ , q) r shift))
--            ∙ ap (_∙ To.β-r q (_ , q) r shift) (!-inv-r (To.β-l q (_ , q) r shift)) ⟩
--       To.β-r q (_ , q) r shift
--           ∎)
--     (λ shift →
--       From.β-l q (_ , q) r shift ∙ From.p' q r shift
--           =⟨ ! $ ap (From.β-l q (_ , q) r shift ∙_) (From.coh q r shift) ⟩
--       From.β-l q (_ , q) r shift ∙ ! (From.β-l q (_ , q) r shift) ∙ From.β-r q (_ , q) r shift
--           =⟨ ! (∙-assoc (From.β-l q (_ , q) r shift) (! (From.β-l q (_ , q) r shift)) (From.β-r q (_ , q) r shift))
--            ∙ ap (_∙ From.β-r q (_ , q) r shift) (!-inv-r (From.β-l q (_ , q) r shift)) ⟩
--       From.β-r q (_ , q) r shift
--           ∎)

-- -- Lemmas

-- private
--   abstract
--     to-from-template : ∀ {a₀ a₁ b₀ b₁} {q₀₀ : Q a₀ b₀}
--       {q₁₁ : Q a₁ b₁} {q₀₁ : Q a₀ b₁} {q₁₀ : Q a₁ b₀} {r}
--       (params : βPair q₀₀ q₁₁ q₀₁ q₁₀ r) shift
--       → to q₀₀ q₁₁ r (from q₀₀ q₁₁ r [ q₀₁ , shift ]) == [ q₀₁ , shift ]
--     to-from-template {q₀₀ = q₀₀} {q₁₁} {q₀₁} {q₁₀} {r} params shift =
--       to q₀₀ q₁₁ r (from q₀₀ q₁₁ r [ q₀₁ , shift ])
--         =⟨ ap (to q₀₀ q₁₁ r) $ from-β shift ⟩
--       to q₀₀ q₁₁ r [ q₁₀ , ! path ∙' shift ]
--         =⟨ to-β (! path ∙' shift) ⟩
--       [ q₀₁ , path ∙' ! path ∙' shift ]
--         =⟨ ap (λ p → [ q₀₁ , p ]) $ ! (∙'-assoc path (! path) shift) ∙ ap (_∙' shift) (!-inv'-r path) ∙ ∙'-unit-l shift ⟩
--       [ q₀₁ , shift ]
--         =∎
--       where open βPair params

-- module FromTo {a₁ b₀} (q₁₀ : Q a₁ b₀) where
--   -- upper
--   U = To.U q₁₀
--   u₀ = To.u₀ q₁₀
--   -- lower
--   V = To.V q₁₀
--   v₀ = To.v₀ q₁₀

--   P : U → V → Type (lmax i (lmax j k))
--   P u v = (r : bmleft (fst u) == bmright (fst v))
--     → (shift : bmglue (snd u) ∙' ! (bmglue q₁₀) ∙' bmglue (snd v) == r)
--     → from (snd u) (snd v) r (to (snd u) (snd v) r [ q₁₀ , shift ]) == [ q₁₀ , shift ]

--   abstract
--     template : ∀ (u : U) (v : V) r shift q₀₁
--       → βPair (snd u) (snd v) q₀₁ q₁₀ r
--       → from (snd u) (snd v) r (to (snd u) (snd v) r [ q₁₀ , shift ]) == [ q₁₀ , shift ]
--     template (_ , q₀₀) (_ , q₁₁) r shift q₀₁ params =
--       from q₀₀ q₁₁ r (to q₀₀ q₁₁ r [ q₁₀ , shift ])
--         =⟨ ap (from q₀₀ q₁₁ r) $ to-β shift ⟩
--       from q₀₀ q₁₁ r [ q₀₁ , path ∙' shift ]
--         =⟨ from-β (path ∙' shift) ⟩
--       [ q₁₀ , ! path ∙' path ∙' shift ]
--         =⟨ ap (λ p → [ q₁₀ , p ]) $ ! (∙'-assoc (! path) path shift) ∙ ap (_∙' shift) (!-inv'-l path) ∙ ∙'-unit-l shift ⟩
--       [ q₁₀ , shift ]
--         =∎
--       where open βPair params

--   f = λ u r shift → template u v₀ r shift (snd u) (βpair-bmleft (snd u) q₁₀ r)
--   g = λ v r shift → template u₀ v r shift (snd v) (βpair-bmright q₁₀ (snd v) r)

--   abstract
--     p : f u₀ == g v₀
--     p = λ= λ r → λ= λ shift → ap (template u₀ v₀ r shift q₁₀) (βpair-glue q₁₀ r)

--   args : WedgeExt.args {A = U} {a₀ = u₀} {B = V} {b₀ = v₀}
--   args = record {
--     n = n; m = m;
--     cA = g-conn b₀;
--     cB = f-conn a₁;
--     P = λ u v → swap-level $ P u v , Π-level λ _ → Π-level λ _ → =-preserves-level Trunc-level;
--     f = f; g = g; p = p}

--   abstract
--     ext : ∀ u v → P u v
--     ext = WedgeExt.ext args

-- abstract
--   from-to' : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁) r fiber
--     → from q₀₀ q₁₁ r (to' q₀₀ q₁₁ r fiber) == [ fiber ]
--   from-to' q₀₀ q₁₁ r (q₁₀ , shift) = FromTo.ext q₁₀ (_ , q₀₀) (_ , q₁₁) r shift

--   from-to : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁) r fiber
--     → from q₀₀ q₁₁ r (to q₀₀ q₁₁ r fiber) == fiber
--   from-to q₀₀ q₁₁ r = Trunc-elim (λ _ → =-preserves-level Trunc-level) (from-to' q₀₀ q₁₁ r)

-- module ToFrom {a₀ b₁} (q₀₁ : Q a₀ b₁) where
--   -- upper
--   U = From.U q₀₁
--   u₀ = From.u₀ q₀₁
--   -- lower
--   V = From.V q₀₁
--   v₀ = From.v₀ q₀₁

--   P : U → V → Type (lmax i (lmax j k))
--   P u v = (r : bmleft a₀ == bmright b₁)
--     → (shift : bmglue q₀₁ == r)
--     → to (snd v) (snd u) r (from (snd v) (snd u) r [ q₀₁ , shift ]) == [ q₀₁ , shift ]

--   abstract
--     template : ∀ (u : U) (v : V) r shift q₁₀
--       → βPair (snd v) (snd u) q₀₁ q₁₀ r
--       → to (snd v) (snd u) r (from (snd v) (snd u) r [ q₀₁ , shift ]) == [ q₀₁ , shift ]
--     template (_ , q₁₁) (_ , q₀₀) r shift q₁₀ params =
--       to q₀₀ q₁₁ r (from q₀₀ q₁₁ r [ q₀₁ , shift ])
--         =⟨ ap (to q₀₀ q₁₁ r) $ from-β shift ⟩
--       to q₀₀ q₁₁ r [ q₁₀ , ! path ∙' shift ]
--         =⟨ to-β (! path ∙' shift) ⟩
--       [ q₀₁ , path ∙' ! path ∙' shift ]
--         =⟨ ap (λ p → [ q₀₁ , p ]) $ ! (∙'-assoc path (! path) shift) ∙ ap (_∙' shift) (!-inv'-r path) ∙ ∙'-unit-l shift ⟩
--       [ q₀₁ , shift ]
--         =∎
--       where open βPair params

--   f = λ u r shift → template u v₀ r shift (snd u) (βpair-bmleft q₀₁ (snd u) r)
--   g = λ v r shift → template u₀ v r shift (snd v) (βpair-bmright (snd v) q₀₁ r)

--   abstract
--     p : f u₀ == g v₀
--     p = λ= λ r → λ= λ shift → ap (template u₀ v₀ r shift q₀₁) (βpair-glue q₀₁ r)

--   args : WedgeExt.args {A = U} {a₀ = u₀} {B = V} {b₀ = v₀}
--   args = record {
--     n = n; m = m;
--     cA = g-conn b₁;
--     cB = f-conn a₀;
--     P = λ u v → swap-level $ P u v , Π-level λ _ → Π-level λ _ → =-preserves-level Trunc-level;
--     f = f; g = g; p = p}

--   abstract
--     ext : ∀ u v → P u v
--     ext = WedgeExt.ext args

-- abstract
--   to-from' : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁) r fiber
--     → to q₀₀ q₁₁ r (from' q₀₀ q₁₁ r fiber) == [ fiber ]
--   to-from' q₀₀ q₁₁ r (q₀₁ , shift) = ToFrom.ext q₀₁ (_ , q₁₁) (_ , q₀₀) r shift

--   to-from : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁) r fiber
--     → to q₀₀ q₁₁ r (from q₀₀ q₁₁ r fiber) == fiber
--   to-from q₀₀ q₁₁ r = Trunc-elim (λ _ → =-preserves-level Trunc-level) (to-from' q₀₀ q₁₁ r)

-- eqv : ∀ {a₀ a₁ b₀ b₁} (q₀₀ : Q a₀ b₀) (q₁₁ : Q a₁ b₁) r
--   → Trunc (m +2+ n) (hfiber (λ q₁₀ → bmglue q₀₀ ∙' ! (bmglue q₁₀) ∙' bmglue q₁₁) r)
--   ≃ Trunc (m +2+ n) (hfiber bmglue r)
-- eqv q₀₀ q₁₁ r = equiv (to q₀₀ q₁₁ r) (from q₀₀ q₁₁ r) (to-from q₀₀ q₁₁ r) (from-to q₀₀ q₁₁ r)
