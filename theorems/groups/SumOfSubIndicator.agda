{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- Maybe it is actually easier to prove [sum-subindicator]
   and then derive the other lemma. -}

module groups.SumOfSubIndicator where

module _ {i j k} (G : Group i) {A : Type j} {B : Type k}
  {I} (p : Fin I ≃ Coprod A B) (f : B → Group.El G) b*
  (sub-indicator : ∀ {b} → b ≠ b* → f b == Group.ident G)
  where
 
  open Group G

  abstract
    private
      subsum-r-prefix : ∀ m o {I}
        (p : Fin (ℕ-S^' (S m) (ℕ-S^' o I)) ≃ Coprod A B)
        → inr b* == –> p (Fin-S^' m (ℕ-S^' o I , ltS))
        → subsum-r (–> p ∘ Fin-S^' (S m) ∘ Fin-S^' o) f == ident
      subsum-r-prefix m o {I = O} p _ = idp
      subsum-r-prefix m o {I = S I} p path₀ =
        ap2 comp
          (subsum-r-prefix m (S o) p path₀)
          (Coprod-elim
            {C = λ c →
              c == –> p (Fin-S^' (S m) (Fin-S^' o (I , ltS)))
              →  Coprod-rec (cst ident) f c
              == ident}
            (λ _ _ → idp)
            (λ b path₁ → sub-indicator (λ b=b* → –>-≠ p (Fin-S^'-≠ m (ltSR≠ltS _)) (! path₁ ∙ ap inr b=b* ∙' path₀)))
            (–> p (Fin-S^' (S m) (Fin-S^' o (I , ltS)))) idp)
        ∙ unit-l _

      subsum-r-all' : ∀ m {I} (p : Fin (ℕ-S^' m I) ≃ Coprod A B)
        → (<I* : Fin I) → inr b* == –> p (Fin-S^' m <I*)
        → subsum-r (–> p ∘ Fin-S^' m) f == f b*
      subsum-r-all' m p (I , ltS) path₀ =
        ap2 comp
          (subsum-r-prefix m 0 {I = I} p path₀)
          (ap (Coprod-rec (cst ident) f) (! path₀))
        ∙ unit-l _
      subsum-r-all' m {I = S I} p (o , ltSR o<I) path₀ =
        ap2 comp
          (subsum-r-all' (S m) {I} p (o , o<I) path₀)
          (Coprod-elim
            {C = λ c →
              c == –> p (Fin-S^' m (I , ltS))
              → Coprod-rec (cst ident) f c == ident}
            (λ _ _ → idp)
            (λ b path₁ → sub-indicator (λ b=b* → –>-≠ p (Fin-S^'-≠ m (ltS≠ltSR _)) (! path₁ ∙ ap inr b=b* ∙' path₀)))
            (–> p (Fin-S^' m (I , ltS))) idp)
        ∙ unit-r _

    subsum-r-subindicator : subsum-r (–> p) f == f b*
    subsum-r-subindicator = subsum-r-all' 0 p (<– p (inr b*)) (! (<–-inv-r p (inr b*)))

module _ {i} (G : Group i) {I} (f : Fin I → Group.El G) <I*
  (sub-indicator : ∀ {<I} → <I ≠ <I* → f <I == Group.ident G)
  where

  sum-subindicator : Group.sum G f == f <I*
  sum-subindicator = subsum-r-subindicator G (⊔₁-Empty (Fin I) ⁻¹) f <I* sub-indicator
