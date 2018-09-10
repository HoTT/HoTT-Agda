{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Int
open import lib.types.List
open import lib.types.Word
open import lib.types.SetQuotient
open import lib.groups.Homomorphism

module lib.groups.GeneratedGroup {i m} where

module GeneratedGroup (A : Type i) (R : Rel (Word A) m) where

  -- [qwr-sym] is not needed, but it seems more principled to
  -- make [QuotWordRel] an equivalence relation.
  data QuotWordRel : Word A → Word A → Type (lmax i m) where
    qwr-refl : ∀ {l₁ l₂} → l₁ == l₂ → QuotWordRel l₁ l₂
    qwr-trans : ∀ {l₁ l₂ l₃} → QuotWordRel l₁ l₂ → QuotWordRel l₂ l₃ → QuotWordRel l₁ l₃
    qwr-sym : ∀ {l₁ l₂} → QuotWordRel l₁ l₂ → QuotWordRel l₂ l₁
    qwr-cong : ∀ {l₁ l₂ l₃ l₄} → QuotWordRel l₁ l₂ → QuotWordRel l₃ l₄ → QuotWordRel (l₁ ++ l₃) (l₂ ++ l₄)
    qwr-flip-r : ∀ x₁ → QuotWordRel (x₁ :: flip x₁ :: nil) nil
    qwr-rel : ∀ {l₁ l₂} → R l₁ l₂ → QuotWordRel l₁ l₂

  qwr-cong-l : ∀ {l₁ l₂} → QuotWordRel l₁ l₂ → ∀ l₃ → QuotWordRel (l₁ ++ l₃) (l₂ ++ l₃)
  qwr-cong-l qwr l₃ = qwr-cong qwr (qwr-refl idp)

  qwr-cong-r : ∀ l₁ {l₂ l₃} → QuotWordRel l₂ l₃ → QuotWordRel (l₁ ++ l₂) (l₁ ++ l₃)
  qwr-cong-r l₁ qwr = qwr-cong (qwr-refl (idp {a = l₁})) qwr

  abstract
    infixr 10 _qwr⟨_⟩_
    infixr 10 _qwr⟨id⟩_
    infix  15 _qwr∎

    _qwr⟨_⟩_ : ∀  l₁ {l₂ l₃} → QuotWordRel l₁ l₂ → QuotWordRel l₂ l₃ → QuotWordRel l₁ l₃
    _ qwr⟨ p ⟩ q = qwr-trans p q

    _qwr⟨id⟩_ : ∀  l₁ {l₂} → QuotWordRel l₁ l₂ → QuotWordRel l₁ l₂
    _ qwr⟨id⟩ q = q

    _qwr∎ : ∀ l → QuotWordRel l l
    _ qwr∎ = qwr-refl idp

  qwr-flip-l : ∀ x₁ → QuotWordRel (flip x₁ :: x₁ :: nil) nil
  qwr-flip-l x₁ =
    flip x₁ :: x₁ :: nil
      qwr⟨ qwr-refl (ap (λ s → flip x₁ :: s :: nil) (! (flip-flip x₁))) ⟩
    flip x₁ :: flip (flip x₁) :: nil
      qwr⟨ qwr-flip-r (flip x₁) ⟩
    nil qwr∎

  -- The quotient
  QuotWord : Type (lmax i m)
  QuotWord = SetQuot QuotWordRel

  qw[_] : Word A → QuotWord
  qw[_] = q[_]

  {-
    In the case where this module is used to realize some free construction F
    (e.g. free group, free abelian group), this function becomes the unit of
    the adjunction F -| U (where U is the forgetful functor).
  -}
  insert : A → QuotWord
  insert a = qw[ inl a :: nil ]

  module QuotWordElim {k} {P : QuotWord → Type k}
    {{_ : {x : QuotWord} → is-set (P x)}} (incl* : (a : Word A) → P qw[ a ])
    (rel* : ∀ {a₁ a₂} (r : QuotWordRel a₁ a₂) → incl* a₁ == incl* a₂ [ P ↓ quot-rel r ])
    = SetQuotElim incl* rel*
  open QuotWordElim public renaming (f to QuotWord-elim) hiding (quot-rel-β)

  module QuotWordRec {k} {B : Type k} {{_ : is-set B}} (incl* : Word A → B)
    (rel* : ∀ {a₁ a₂} (r : QuotWordRel a₁ a₂) → incl* a₁ == incl* a₂)
    = SetQuotRec incl* rel*
  open QuotWordRec public renaming (f to QuotWord-rec)

  private
    infixl 80 _⊞_
    _⊞_ : QuotWord → QuotWord → QuotWord
    _⊞_ = QuotWord-rec
      (λ l₁ → QuotWord-rec (λ l₂ → qw[ l₁ ++ l₂ ])
        (λ r → quot-rel $ qwr-cong-r l₁ r))
      (λ {l₁} {l₁'} r → λ= $ QuotWord-elim
        (λ l₂ → quot-rel $ qwr-cong-l r l₂)
        (λ _ → prop-has-all-paths-↓))

    abstract
      qwr-cancel-l : ∀ l
        → QuotWordRel (Word-inverse l ++ l) nil
      qwr-cancel-l nil = qwr-refl idp
      qwr-cancel-l (x :: l) =
        Word-inverse (x :: l) ++ (x :: l)
          qwr⟨id⟩
        (Word-inverse l ++ (flip x :: nil)) ++ (x :: l)
          qwr⟨ qwr-refl (++-assoc (reverse (Word-flip l)) (flip x :: nil) (x :: l)) ⟩
        Word-inverse l ++ ((flip x :: nil) ++ (x :: l))
          qwr⟨id⟩
        Word-inverse l ++ (flip x :: x :: l)
          qwr⟨ qwr-cong-r (reverse (Word-flip l)) (qwr-cong-l (qwr-flip-l x) l) ⟩
        Word-inverse l ++ l
          qwr⟨ qwr-cancel-l l ⟩
        nil qwr∎

      qwr-cancel-r : ∀ l
        → QuotWordRel (l ++ Word-inverse l) nil
      qwr-cancel-r l =
        l ++ Word-inverse l
          qwr⟨ qwr-refl (ap (_++ Word-inverse l) (! (Word-inverse-inverse l))) ⟩
        Word-inverse (Word-inverse l) ++ Word-inverse l
          qwr⟨ qwr-cancel-l (Word-inverse l) ⟩
        nil qwr∎

      qwr-cong-inverse : ∀ {l₁ l₂}
        → QuotWordRel l₁ l₂ → QuotWordRel (Word-inverse l₁) (Word-inverse l₂)
      qwr-cong-inverse {l₁} {l₂} r =
        Word-inverse l₁
          qwr⟨ qwr-refl (! (++-unit-r (Word-inverse l₁))) ⟩
        Word-inverse l₁ ++ nil
          qwr⟨ qwr-cong-r (Word-inverse l₁) (qwr-sym (qwr-cancel-r l₂)) ⟩
        Word-inverse l₁ ++ (l₂ ++ Word-inverse l₂)
          qwr⟨ qwr-cong-r (Word-inverse l₁) (qwr-cong-l (qwr-sym r) (Word-inverse l₂)) ⟩
        reverse (Word-flip l₁) ++ (l₁ ++ Word-inverse l₂)
          qwr⟨ qwr-refl (! (++-assoc (Word-inverse l₁) l₁ (Word-inverse l₂))) ⟩
        (Word-inverse l₁ ++ l₁) ++ Word-inverse l₂
          qwr⟨ qwr-cong-l (qwr-cancel-l l₁) (Word-inverse l₂) ⟩
        Word-inverse l₂ qwr∎

    ⊟ : QuotWord → QuotWord
    ⊟ = QuotWord-rec (qw[_] ∘ Word-inverse)
      (λ r → quot-rel $ qwr-cong-inverse r)

    ⊞-unit : QuotWord
    ⊞-unit = qw[ nil ]

    abstract
      ⊞-unit-l : ∀ g → ⊞-unit ⊞ g == g
      ⊞-unit-l = QuotWord-elim
        (λ _ → idp)
        (λ _ → prop-has-all-paths-↓)

      ⊞-assoc : ∀ g₁ g₂ g₃ → (g₁ ⊞ g₂) ⊞ g₃ == g₁ ⊞ (g₂ ⊞ g₃)
      ⊞-assoc = QuotWord-elim
        (λ l₁ → QuotWord-elim
          (λ l₂ → QuotWord-elim
            (λ l₃ → ap qw[_] $ ++-assoc l₁ l₂ l₃)
            (λ _ → prop-has-all-paths-↓))
          (λ _ → prop-has-all-paths-↓))
        (λ _ → prop-has-all-paths-↓)

      ⊟-inv-l : ∀ g → (⊟ g) ⊞ g == ⊞-unit
      ⊟-inv-l = QuotWord-elim
        (λ l → quot-rel (qwr-cancel-l l))
        (λ _ → prop-has-all-paths-↓)

  QuotWord-group-structure : GroupStructure QuotWord
  QuotWord-group-structure = record
    { ident = ⊞-unit
    ; inv = ⊟
    ; comp = _⊞_
    ; unit-l = ⊞-unit-l
    ; assoc = ⊞-assoc
    ; inv-l = ⊟-inv-l
    }

  GenGroup : Group (lmax i m)
  GenGroup = group _ QuotWord-group-structure

  module GenGroup = Group GenGroup
  open GenGroup using (El) public

  abstract
    pres-exp : ∀ (a : A) z →
      qw[ Word-exp a z ] == GenGroup.exp qw[ inl a :: nil ] z
    pres-exp a (pos O) = idp
    pres-exp a (pos (S O)) = idp
    pres-exp a (pos (S (S n))) =
      ap (GenGroup.comp qw[ inl a :: nil ]) (pres-exp a (pos (S n)))
    pres-exp a (negsucc O) = idp
    pres-exp a (negsucc (S n)) =
      ap (GenGroup.comp qw[ inr a :: nil ]) (pres-exp a (negsucc n))

  -- freeness
  module HomomorphismEquiv {j} (G : Group j) where

    private
      module G = Group G
    open RelationRespectingFunctions A R G public

    module _ (fun : RelationRespectingFunction) where

      private
        module fun = RelationRespectingFunction fun
        f* = fun.f

        abstract
          Word-extendᴳ-emap : ∀ {l₁ l₂}
            → QuotWordRel l₁ l₂
            → Word-extendᴳ G f* l₁ == Word-extendᴳ G f* l₂
          Word-extendᴳ-emap (qwr-refl idp) = idp
          Word-extendᴳ-emap (qwr-trans qwr qwr₁) = (Word-extendᴳ-emap qwr) ∙ (Word-extendᴳ-emap qwr₁)
          Word-extendᴳ-emap (qwr-sym qwr) = ! (Word-extendᴳ-emap qwr)
          Word-extendᴳ-emap (qwr-flip-r x) =
            G.comp (PlusMinus-extendᴳ G f* x) (PlusMinus-extendᴳ G f* (flip x))
              =⟨ ap (G.comp (PlusMinus-extendᴳ G f* x)) (PlusMinus-extendᴳ-flip G f* x) ⟩
            G.comp (PlusMinus-extendᴳ G f* x) (G.inv (PlusMinus-extendᴳ G f* x))
              =⟨ G.inv-r (PlusMinus-extendᴳ G f* x) ⟩
            G.ident =∎
          Word-extendᴳ-emap (qwr-cong {l₁} {l₂} {l₃} {l₄} qwr qwr') =
            Word-extendᴳ G f* (l₁ ++ l₃)
              =⟨ Word-extendᴳ-++ G f* l₁ l₃ ⟩
            G.comp (Word-extendᴳ G f* l₁) (Word-extendᴳ G f* l₃)
              =⟨ ap2 G.comp (Word-extendᴳ-emap qwr) (Word-extendᴳ-emap qwr') ⟩
            G.comp (Word-extendᴳ G f* l₂) (Word-extendᴳ G f* l₄)
              =⟨ ! (Word-extendᴳ-++ G f* l₂ l₄) ⟩
            Word-extendᴳ G f* (l₂ ++ l₄) =∎
          Word-extendᴳ-emap (qwr-rel r) = fun.respects r

      extend : (GenGroup →ᴳ G)
      extend = record {M} where
        module M where
          f : QuotWord → G.El
          f = QuotWord-rec (Word-extendᴳ G f*)
              (λ r → Word-extendᴳ-emap r)
          abstract
            pres-comp : preserves-comp GenGroup.comp G.comp f
            pres-comp =
              QuotWord-elim
                (λ l₁ → QuotWord-elim
                  (λ l₂ → Word-extendᴳ-++ G f* l₁ l₂)
                  (λ _ → prop-has-all-paths-↓))
                (λ _ → prop-has-all-paths-↓)

    private
      module Lemma (hom : GenGroup →ᴳ G) where
        private
          open GroupHom hom
          restr : A → G.El
          restr a = f qw[ inl a :: nil ]

        abstract
          PlusMinus-extendᴳ-hom : ∀ x → PlusMinus-extendᴳ G restr x == f qw[ x :: nil ]
          PlusMinus-extendᴳ-hom (inl x) = idp
          PlusMinus-extendᴳ-hom (inr x) = ! $ pres-inv qw[ inl x :: nil ]

          Word-extendᴳ-hom : ∀ l → Word-extendᴳ G restr l == f qw[ l ]
          Word-extendᴳ-hom nil = ! pres-ident
          Word-extendᴳ-hom (x :: nil) = PlusMinus-extendᴳ-hom x
          Word-extendᴳ-hom (x :: l@(_ :: _)) =
            G.comp (PlusMinus-extendᴳ G restr x) (Word-extendᴳ G restr l)
              =⟨ ap2 G.comp (PlusMinus-extendᴳ-hom x) (Word-extendᴳ-hom l) ⟩
            G.comp (f qw[ x :: nil ]) (f qw[ l ])
              =⟨ ! (pres-comp _ _) ⟩
            f qw[ x :: l ] =∎

          restr-respects-rel : ∀ {l₁ l₂} → R l₁ l₂ → Word-extendᴳ G restr l₁ == Word-extendᴳ G restr l₂
          restr-respects-rel {l₁} {l₂} r =
            Word-extendᴳ G restr l₁
              =⟨ Word-extendᴳ-hom l₁ ⟩
            f qw[ l₁ ]
              =⟨ ap f (quot-rel (qwr-rel r)) ⟩
            f qw[ l₂ ]
              =⟨ ! (Word-extendᴳ-hom l₂) ⟩
            Word-extendᴳ G restr l₂ =∎

        restrict : RelationRespectingFunction
        restrict = rel-res-fun restr restr-respects-rel

      open Lemma

    extend-is-equiv : is-equiv extend
    extend-is-equiv = is-eq _ from to-from from-to where
      to = extend
      from = restrict

      abstract
        to-from : ∀ h → to (from h) == h
        to-from h = group-hom= $ λ= $ QuotWord-elim
          (λ l → Word-extendᴳ-hom h l)
          (λ _ → prop-has-all-paths-↓)

        from-to : ∀ fun → from (to fun) == fun
        from-to fun = RelationRespectingFunction= (λ= λ a → idp)

    extend-equiv : RelationRespectingFunction ≃ (GenGroup →ᴳ G)
    extend-equiv = extend , extend-is-equiv
