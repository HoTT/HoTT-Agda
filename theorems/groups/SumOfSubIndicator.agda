{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- Maybe it is actually easier to prove [sum-subindicator]
   and then derive the other lemma. -}

module groups.SumOfSubIndicator where

module _ {i} (G : Group i) where

  open Group G

  abstract
    sum-ident : ∀ {I} (f : Fin I → El)
      → (∀ <I → f <I == ident)
      → sum f == ident
    sum-ident {I = O} f z = idp
    sum-ident {I = S I} f z =
      ap2 comp
        (sum-ident (f ∘ Fin-S) (z ∘ Fin-S))
        (z (I , ltS))
      ∙ unit-l _

    sum-subindicator : ∀ {I} (f : Fin I → El) <I*
      → (sub-indicator : ∀ {<I} → <I ≠ <I* → f <I == ident)
      → sum f == f <I*
    sum-subindicator f (I , ltS) subind =
      ap (λ g → comp g (f (I , ltS)))
        (sum-ident (f ∘ Fin-S) (λ <I → subind (ltSR≠ltS <I)))
      ∙ unit-l _
    sum-subindicator {I = S I} f (m , ltSR m<I) subind =
      ap2 comp
        (sum-subindicator (f ∘ Fin-S) (m , m<I) (subind ∘ Fin-S-≠))
        (subind (ltS≠ltSR (m , m<I)))
      ∙ unit-r _

module _ {i j k} (G : Group i) {A : Type j} {B : Type k}
  {I} (p : Fin I ≃ Coprod A B) (f : B → Group.El G) b*
  (sub-indicator : ∀ {b} → b ≠ b* → f b == Group.ident G)
  where
 
  open Group G

  abstract
    private
      sub-indicator' : ∀ {<I} → <I ≠ <– p (inr b*)
        → Coprod-rec (λ _ → ident) f (–> p <I) == ident
      sub-indicator' {<I} <I≠p⁻¹b* =
        Coprod-elim
          {C = λ c → c ≠ inr b* → Coprod-rec (λ _ → ident) f c == ident}
          (λ _ _ → idp)
          (λ b inrb≠inrb* → sub-indicator (inrb≠inrb* ∘ ap inr))
          (–> p <I) (<I≠p⁻¹b* ∘ equiv-adj p)

    subsum-r-subindicator : subsum-r (–> p) f == f b*
    subsum-r-subindicator =
      sum-subindicator G
        (Coprod-rec (λ _ → ident) f ∘ –> p)
        (<– p (inr b*))
        sub-indicator'
      ∙ ap (Coprod-rec (λ _ → ident) f) (<–-inv-r p (inr b*))
