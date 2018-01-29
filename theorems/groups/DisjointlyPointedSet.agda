{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.DisjointlyPointedSet

module groups.DisjointlyPointedSet where

  diff-and-separate : ∀ {i j} {X : Ptd i} (G : Group j)
    → (de⊙ X → Group.El G) → Group.El G × (MinusPoint X → Group.El G)
  diff-and-separate {X = X} G f =
    f (pt X) , λ x- → Group.diff G (f (fst x-)) (f (pt X))

  shift-and-unite : ∀ {i j} {X : Ptd i} (G : Group j)
    → is-separable X
    → Group.El G × (MinusPoint X → Group.El G) → (de⊙ X → Group.El G)
  shift-and-unite {X = X} G X-sep p x with X-sep x
  ... | inl _ = fst p
  ... | inr pt≠x = Group.comp G (snd p (x , pt≠x)) (fst p)

  diff-and-separate-hom : ∀ {i j} {X : Ptd i} (G : AbGroup j)
    →  Πᴳ (de⊙ X) (λ _ → AbGroup.grp G)
    →ᴳ AbGroup.grp G ×ᴳ Πᴳ (MinusPoint X) (λ _ → AbGroup.grp G)
  diff-and-separate-hom {X = X} G = group-hom (diff-and-separate grp) lemma where
    open AbGroup G
    abstract
      lemma : preserves-comp
                (Group.comp (Πᴳ (de⊙ X) (λ _ → AbGroup.grp G)))
                (Group.comp (AbGroup.grp G ×ᴳ Πᴳ (MinusPoint X) (λ _ → AbGroup.grp G)))
                (diff-and-separate grp)
      lemma f₀ f₁ = pair×= idp
        (λ= λ x- → diff-comp (f₀ (fst x-)) (f₁ (fst x-)) (f₀ (pt X)) (f₁ (pt X)))

  diff-and-separate-is-equiv : ∀ {i j} {X : Ptd i} (G : Group j)
    → is-separable X → is-equiv (diff-and-separate {X = X} G)
  diff-and-separate-is-equiv {X = X} G X-sep = is-eq to from to-from (λ= ∘ from-to)
    where
      open Group G
      to = diff-and-separate {X = X} G
      from = shift-and-unite {X = X} G X-sep

      abstract
        fst-to-from : ∀ p → fst (to (from p)) == fst p
        fst-to-from _ with X-sep (pt X)
        ... | inl _ = idp
        ... | inr pt≠pt = ⊥-rec (pt≠pt idp)
        
        snd-to-from : ∀ p x → snd (to (from p)) x == snd p x
        snd-to-from p x with X-sep (fst x)
        ... | inl pt=x = ⊥-rec (snd x pt=x)
        ... | inr pt≠x with X-sep (pt X)
        ...   | inl _ = assoc (snd p (fst x , pt≠x)) (fst p) (inv (fst p))
                      ∙ ap (comp (snd p (fst x , pt≠x))) (inv-r (fst p))
                      ∙ unit-r (snd p (fst x , pt≠x))
                      ∙ ap (λ neq → snd p (fst x , neq)) (prop-has-all-paths _ _)
        ...   | inr pt≠pt = ⊥-rec (pt≠pt idp)

        to-from : ∀ p → to (from p) == p
        to-from p = pair×= (fst-to-from p) (λ= (snd-to-from p))

        from-to : ∀ f x → from (to f) x == f x
        from-to f x with X-sep x
        ... | inl idp = idp
        ... | inr _ = assoc (f x) (inv (f (pt X))) (f (pt X))
                    ∙ ap (comp (f x)) (inv-l (f (pt X)))
                    ∙ unit-r (f x)

  diff-and-separate-iso : ∀ {i j} {X : Ptd i} (G : AbGroup j)
    → is-separable X
    →  Πᴳ (de⊙ X) (λ _ → AbGroup.grp G)
    ≃ᴳ AbGroup.grp G ×ᴳ Πᴳ (MinusPoint X) (λ _ → AbGroup.grp G)
  diff-and-separate-iso G X-sep =
    diff-and-separate-hom G , diff-and-separate-is-equiv (AbGroup.grp G) X-sep
