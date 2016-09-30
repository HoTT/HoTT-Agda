open import HoTT
-- open import homotopy.FunctionOver
open import groups.HomSequence

module groups.ExactSequence where

is-exact-seq : ∀ {i} {G H : Group i}
  → HomSequence G H → Type i
is-exact-seq (_ ⊣|ᴳ) = Lift ⊤
is-exact-seq (_ →⟨ φ ⟩ᴳ _ ⊣|ᴳ) = Lift ⊤
is-exact-seq (_ →⟨ φ ⟩ᴳ _ →⟨ ψ ⟩ᴳ seq) =
  is-exact φ ψ × is-exact-seq (_ →⟨ ψ ⟩ᴳ seq)

{- equivalences preserve exactness -}

abstract
  hom-pair-equiv-preserves-exact : ∀ {i₀ i₁ j₀ j₁ l₀ l₁}
    {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁} {K₀ : Group l₀} {K₁ : Group l₁}
    {φ₀ : G₀ →ᴳ H₀} {ψ₀ : H₀ →ᴳ K₀} {φ₁ : G₁ →ᴳ H₁} {ψ₁ : H₁ →ᴳ K₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
    → CommSquareᴳ φ₀ φ₁ ξG ξH
    → CommSquareᴳ ψ₀ ψ₁ ξH ξK
    → is-equiv (GroupHom.f ξG) → is-equiv (GroupHom.f ξH) → is-equiv (GroupHom.f ξK)
    → is-exact φ₀ ψ₀
    → is-exact φ₁ ψ₁
  hom-pair-equiv-preserves-exact {K₀ = K₀} {K₁} {φ₀ = φ₀} {ψ₀} {φ₁} {ψ₁} {ξG} {ξH} {ξK}
    (comm-sqrᴳ φ□) (comm-sqrᴳ ψ□) ξG-is-equiv ξH-is-equiv ξK-is-equiv exact₀
    = record {
      im-sub-ker = λ h₁ → Trunc-rec (SubgroupProp.level (ker-propᴳ ψ₁) h₁)
        (λ{(g₁ , φ₁g₁=h₁) →
          ψ₁.f h₁
            =⟨ ap ψ₁.f $ ! $ ξH.f-g h₁ ⟩
          ψ₁.f (ξH.f (ξH.g h₁))
            =⟨ ! $ ψ□ (ξH.g h₁) ⟩
          ξK.f (ψ₀.f (ξH.g h₁))
            =⟨ ap ξK.f $ im-sub-ker exact₀ (ξH.g h₁) [ _,_ (ξG.g g₁) $
                φ₀.f (ξG.g g₁)
                  =⟨ ! (ξH.g-f (φ₀.f (ξG.g g₁))) ⟩
                ξH.g (ξH.f (φ₀.f (ξG.g g₁)))
                  =⟨ ap ξH.g $ φ□ (ξG.g g₁) ∙ ap φ₁.f (ξG.f-g g₁) ∙ φ₁g₁=h₁ ⟩
                ξH.g h₁
                  =∎ ] ⟩
          ξK.f (Group.ident K₀)
            =⟨ ξK.pres-ident ⟩
          Group.ident K₁
            =∎});
      ker-sub-im = λ h₁ ψ₁h₁=0 →
        Trunc-rec (SubgroupProp.level (im-propᴳ φ₁) h₁)
          (λ{(g₀ , φ₀g₀=ξH⁻¹h₁) → [ _,_ (ξG.f g₀) $
            φ₁.f (ξG.f g₀)
              =⟨ ! $ φ□ g₀ ⟩
            ξH.f (φ₀.f g₀)
              =⟨ ap ξH.f φ₀g₀=ξH⁻¹h₁ ⟩
            ξH.f (ξH.g h₁)
              =⟨ ξH.f-g h₁ ⟩
            h₁
              =∎ ]})
          (ker-sub-im exact₀ (ξH.g h₁) $
            ψ₀.f (ξH.g h₁)
              =⟨ ! $ ξK.g-f (ψ₀.f (ξH.g h₁)) ⟩
            ξK.g (ξK.f (ψ₀.f (ξH.g h₁)))
              =⟨ ap ξK.g $ ψ□ (ξH.g h₁) ∙ ap ψ₁.f (ξH.f-g h₁) ∙ ψ₁h₁=0 ⟩
            ξK.g (Group.ident K₁)
              =⟨ GroupHom.pres-ident ξK.g-hom ⟩
            Group.ident K₀
              =∎)}
    where
      module φ₀ = GroupHom φ₀
      module φ₁ = GroupHom φ₁
      module ψ₀ = GroupHom ψ₀
      module ψ₁ = GroupHom ψ₁
      module ξG = GroupIso (ξG , ξG-is-equiv)
      module ξH = GroupIso (ξH , ξH-is-equiv)
      module ξK = GroupIso (ξK , ξK-is-equiv)

  hom-seq-equiv-preserves-exact : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    → HomSeqEquiv seq₀ seq₁ ξG ξH
    → is-exact-seq seq₀ → is-exact-seq seq₁
  hom-seq-equiv-preserves-exact ((_ ↓|ᴳ) , _) _ = lift tt
  hom-seq-equiv-preserves-exact ((_ ↓⟨ _ ⟩ᴳ _ ↓|ᴳ) , _) _ = lift tt
  hom-seq-equiv-preserves-exact
    ( (ξG ↓⟨ φ□ ⟩ᴳ _↓⟨_⟩ᴳ_ ξH {ξK} ψ□ seq-map)
    , (ξG-ise , ξH-ise , seq-map-ise))
    (φ₀-ψ₀-is-exact , ψ₀-seq₀-is-exact-seq) =
      hom-pair-equiv-preserves-exact
        φ□ ψ□ ξG-ise ξH-ise (is-seqᴳ-equiv.head seq-map-ise)
        φ₀-ψ₀-is-exact ,
      hom-seq-equiv-preserves-exact
        ((ξH ↓⟨ ψ□ ⟩ᴳ seq-map) , (ξH-ise , seq-map-ise))
        ψ₀-seq₀-is-exact-seq

{-
  hom-seq-equiv-preserves'-exact : ∀ {i} {G₀ G₁ H₀ H₁ : Group i}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} (seq-map : HomSeqMap seq₀ seq₁ ξG ξH)
    → is-seqᴳ-equiv seq-map → is-exact-seq seq₁ → is-exact-seq seq₀
  hom-seq-equiv-preserves'-exact :
-}
{-
data is-exact-seq {i} : {G H : Group i} → HomSequence G H → Type (lsucc i) where
  exact-seq-zero : {G : Group i} → is-exact-seq (G ⊣|)
  exact-seq-one : {G H : Group i} {φ : G →ᴳ H} → is-exact-seq (G ⟨ φ ⟩→ H ⊣|)
  exact-seq-more : {G H K J : Group i} {φ : G →ᴳ H} {ψ : H →ᴳ K}
    {diag : HomSequence K J} → is-exact φ ψ
    → is-exact-seq (H ⟨ ψ ⟩→ diag) → is-exact-seq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ diag)

private
  exact-get-type : ∀ {i} {G H : Group i} → HomSequence G H → ℕ → Type i
  exact-get-type (G ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ H ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ (H ⟨ ψ ⟩→ s)) O = is-exact φ ψ
  exact-get-type (_ ⟨ _ ⟩→ s) (S n) = exact-get-type s n

exact-get : ∀ {i} {G H : Group i} {diag : HomSequence G H}
  → is-exact-seq diag → (n : ℕ) → exact-get-type diag n
exact-get exact-seq-zero _ = lift unit
exact-get exact-seq-one _ = lift unit
exact-get (exact-seq-more ex s) O = ex
exact-get (exact-seq-more ex s) (S n) = exact-get s n

private
  exact-build-arg-type : ∀ {i} {G H : Group i} → HomSequence G H → List (Type i)
  exact-build-arg-type (G ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) =
    is-exact φ ψ :: exact-build-arg-type (H ⟨ ψ ⟩→ s)

  exact-build-helper : ∀ {i} {G H : Group i} (seq : HomSequence G H)
    → HList (exact-build-arg-type seq) → is-exact-seq seq
  exact-build-helper (G ⊣|) nil = exact-seq-zero
  exact-build-helper (G ⟨ φ ⟩→ H ⊣|) nil = exact-seq-one
  exact-build-helper (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) (ie :: ies) =
    exact-seq-more ie (exact-build-helper (H ⟨ ψ ⟩→ s) ies)

exact-build : ∀ {i} {G H : Group i} (seq : HomSequence G H)
  → hlist-curry-type (exact-build-arg-type seq) (λ _ → is-exact-seq seq)
exact-build seq = hlist-curry (exact-build-helper seq)

private
  hom-seq-snoc : ∀ {i} {G H K : Group i}
    → HomSequence G H → (H →ᴳ K) → HomSequence G K
  hom-seq-snoc (G ⊣|) ψ = G ⟨ ψ ⟩→ _ ⊣|
  hom-seq-snoc (G ⟨ φ ⟩→ s) ψ = G ⟨ φ ⟩→ hom-seq-snoc s ψ

hom-seq-concat : ∀ {i} {G H K : Group i}
  → HomSequence G H → HomSequence H K → HomSequence G K
hom-seq-concat (G ⊣|) s₂ = s₂
hom-seq-concat (G ⟨ φ ⟩→ s₁) s₂ = G ⟨ φ ⟩→ (hom-seq-concat s₁ s₂)

abstract
  exact-concat : ∀ {i} {G H K L : Group i}
    {seq₁ : HomSequence G H} {φ : H →ᴳ K} {seq₂ : HomSequence K L}
    → is-exact-seq (hom-seq-snoc seq₁ φ) → is-exact-seq (H ⟨ φ ⟩→ seq₂)
    → is-exact-seq (hom-seq-concat seq₁ (H ⟨ φ ⟩→ seq₂))
  exact-concat {seq₁ = G ⊣|} exact-seq-one es₂ = es₂
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⊣|} (exact-seq-more ex _) es₂ =
    exact-seq-more ex es₂
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⟨ χ ⟩→ s} (exact-seq-more ex es₁) es₂ =
    exact-seq-more ex (exact-concat {seq₁ = H ⟨ χ ⟩→ s} es₁ es₂)
-}
