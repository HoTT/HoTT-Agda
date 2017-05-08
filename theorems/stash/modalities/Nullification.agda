{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Orthogonality

module stash.modalities.Nullification where

module _ {i} where

  postulate -- HIT
    P⟨_⟩ : (A X : Type i) → Type i
    p[_] : {A X : Type i} → X → P⟨ A ⟩ X
    is-orth : {A X : Type i} → ⟦ A ⊥ P⟨ A ⟩ X ⟧

  module NullElim {A X : Type i} {Q : P⟨ A ⟩ X → Type i}
    (p : (x : P⟨ A ⟩ X) → ⟦ A ⊥ Q x ⟧) (d : (x : X) → Q p[ x ]) where

    postulate
      f : Π (P⟨ A ⟩ X) Q
      p[_]-β : ∀ x → f p[ x ] ↦ d x
    {-# REWRITE p[_]-β #-}

open NullElim public renaming (f to Null-elim)

module _ {i} (A : Type i) where

  NullModality : Modality i
  Modality.is-local NullModality X = ⟦ A ⊥ X ⟧
  Modality.is-local-is-prop NullModality = is-equiv-is-prop
  Modality.◯ NullModality = P⟨ A ⟩ 
  Modality.◯-is-local NullModality = is-orth
  Modality.η NullModality = p[_]
  Modality.◯-elim NullModality = Null-elim
  Modality.◯-elim-β NullModality _ _ _ = idp
  Modality.◯-=-is-local NullModality x y = pths-orth is-orth

module _ {i} (A X : Type i) where

  f-aux : (x : P⟨ Susp A ⟩ X) → P⟨ A ⟩ (x == x)
  f-aux = Null-elim (λ x → susp-≻ A (P⟨ A ⟩ (x == x)) is-orth) (λ x → p[ idp ])
  
  f : (x y : P⟨ Susp A ⟩ X) → x == y → P⟨ A ⟩ (x == y)
  f x .x idp = f-aux x

module _ {i} {A B : Type i} (f : A → B) where

  ap-fib-to : {a₀ a₁ : A} (p : f a₀ == f a₁) → hfiber (ap f) p
    → Σ (hfiber f (f a₀)) (λ α →
       Σ (hfiber f (f a₁)) (λ β →
       Σ (fst α == fst β) (λ q →
       ap f q == snd α ∙ p ∙ ! (snd β))))
  ap-fib-to {a₀} {a₁} .(ap f q) (q , idp) = (a₀ , idp) , (a₁ , idp) , q , ! (∙-unit-r (ap f q))

  postulate
    ap-fib : {a₀ a₁ : A} (p : f a₀ == f a₁) → is-equiv (ap-fib-to p)

  new-ap-fib : {a₀ a₁ : A} (p : f a₀ == f a₁) → hfiber (ap f) p
    → Σ (hfiber f (f a₀)) (λ α →
       Σ (hfiber f (f a₁)) (λ β →
       α == β [ (λ z → hfiber f z) ↓ p ]))
  new-ap-fib = {!!}
  
module _ {i} (A X : Type i) (x y : X) where

  module NMA = Modality (NullModality A)
  module NMSA = Modality (NullModality (Susp A))
  
  -- Okay.  Here is the map in question:
  pΣ : x == y → Path {A = P⟨ Susp A ⟩ X} p[ x ] p[ y ]
  pΣ = ap p[_]

  lemma : NMSA.is-◯-equiv pΣ
  lemma p = NMSA.equiv-preserves-◯-conn ((ap-fib-to p[_] p , ap-fib p[_] p) ⁻¹)
              {!!}

  thm : NMA.is-◯-equiv pΣ
  thm p = {!!}

  -- equiv-preserves-◯-conn : {A B : Type ℓ} → A ≃ B → is-◯-connected A → is-◯-connected B
  -- equiv-preserves-◯-conn e c = equiv-preserves-level (◯-emap e) c

  -- Okay, here's a better explanation: you are simply applying the
  -- full fledged join adjunction formula to the p[_].  I think
  -- the diagonal of this map will have fibers which are exactly
  -- the PathOver description you give above.  Or something
  -- very close to this.  That's the main idea.

  -- Theorem 19.1 of CwA and PA asserts that this map
  -- is A-connected.  Have to trace through the argument.
  -- So we don't contruct a direct inverse ...

  -- He starts by observing that it is ΣA-connected.
  -- Do you have a proof of this?  It should be obvious ...

  -- So by adjuction, loops on this fiber is A-connected.

  -- Then the claim is that you can commute with limits, i.e.
  -- that this is the fiber on loops of the canoncial map.

  -- Right.  This is much clearer.  We'll need some preparation,
  -- but I think this should be quite doable.

  -- this map is fairly easy by adjunction ...
  to : P⟨ A ⟩ (x == y) → (Path {A = P⟨ Susp A ⟩ X} p[ x ] p[ y ])
  to = Null-elim (λ p → adj-orth A (P⟨ Susp A ⟩ X) is-orth p[ x ] p[ y ]) (λ p → ap p[_] p)




