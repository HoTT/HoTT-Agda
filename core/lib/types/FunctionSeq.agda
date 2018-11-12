{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics hiding (take; drop; take-drop-split)
open import lib.types.Pointed
open import lib.types.Paths

module lib.types.FunctionSeq where

infixr 80 _◃∘_
data FunctionSeq {i} : Type i → Type i → Type (lsucc i) where
  idf-seq : {A : Type i} → FunctionSeq A A
  _◃∘_ : {A B C : Type i} (g : B → C) (fs : FunctionSeq A B) → FunctionSeq A C

infix 30 _–→_
_–→_ = FunctionSeq

infix 90 _◃idf
_◃idf : ∀ {i} {A B : Type i} → (A → B) → A –→ B
_◃idf fs = fs ◃∘ idf-seq

compose : ∀ {i} {A B : Type i} → (A –→ B) → A → B
compose idf-seq = idf _
compose (g ◃∘ fs) = g ∘ compose fs

de⊙-seq : ∀ {i} {X Y : Ptd i} → (X ⊙–→ Y) → (de⊙ X –→ de⊙ Y)
de⊙-seq ⊙idf-seq = idf-seq
de⊙-seq (f ◃⊙∘ fs) = fst f ◃∘ de⊙-seq fs

de⊙-seq-⊙compose : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y)
  → compose (de⊙-seq fs) == fst (⊙compose fs)
de⊙-seq-⊙compose ⊙idf-seq = idp
de⊙-seq-⊙compose (f ◃⊙∘ fs) = ap (fst f ∘_) (de⊙-seq-⊙compose fs)

private
  pt-seq' : ∀ {i} {j} {X Y : Ptd i} {C : Type j} (g : de⊙ Y → C) (fs : X ⊙–→ Y)
    → g (compose (de⊙-seq fs) (pt X)) =-= g (pt Y)
  pt-seq' g ⊙idf-seq = []
  pt-seq' g (f ◃⊙∘ fs) =
    pt-seq' (g ∘ fst f) fs ∙∙
    ap g (snd f) ◃∎

pt-seq : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y)
  → compose (de⊙-seq fs) (pt X) =-= pt Y
pt-seq ⊙idf-seq = []
pt-seq (f ◃⊙∘ fs) = pt-seq' (fst f) fs ∙▹ snd f

private
  ⊙compose-pt' : ∀ {i} {j} {X Y : Ptd i} {C : Type j} (g : de⊙ Y → C) (fs : X ⊙–→ Y)
    → ap g (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
      ap g (snd (⊙compose fs)) ◃∎
      =ₛ
      ↯ (pt-seq' g fs) ◃∎
  ⊙compose-pt' g ⊙idf-seq = =ₛ-in idp
  ⊙compose-pt' {_} {_} {X} g (f ◃⊙∘ fs) =
    ap g (app= (ap (fst f ∘_) (de⊙-seq-⊙compose fs)) (pt X)) ◃∙
    ap g (snd (⊙compose (f ◃⊙∘ fs))) ◃∎
      =ₛ₁⟨ 0 & 1 & ∘-ap g (_$ pt X) (ap (fst f ∘_) (de⊙-seq-⊙compose fs)) ∙
                   ∘-ap (λ h → g (h (pt X))) (fst f ∘_) (de⊙-seq-⊙compose fs) ∙
                   ap-∘ (g ∘ fst f) (_$ pt X) (de⊙-seq-⊙compose fs) ⟩
    ap (g ∘ fst f) (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    ap g (snd (⊙compose (f ◃⊙∘ fs))) ◃∎
      =ₛ⟨ 1 & 1 & ap-seq-∙ g (ap (fst f) (snd (⊙compose fs)) ◃∙ snd f ◃∎) ⟩
    ap (g ∘ fst f) (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    ap g (ap (fst f) (snd (⊙compose fs))) ◃∙
    ap g (snd f) ◃∎
      =ₛ₁⟨ 1 & 1 & ∘-ap g (fst f) (snd (⊙compose fs)) ⟩
    ap (g ∘ fst f) (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    ap (g ∘ fst f) (snd (⊙compose fs)) ◃∙
    ap g (snd f) ◃∎
      =ₛ⟨ 0 & 2 & ⊙compose-pt' (g ∘ fst f) fs ⟩
    ↯ (pt-seq' (g ∘ fst f) fs) ◃∙
    ap g (snd f) ◃∎
      =ₛ₁⟨ ! (↯-∙∙ (pt-seq' (g ∘ fst f) fs) (ap g (snd f) ◃∎)) ⟩
    ↯ (pt-seq' (g ∘ fst f) fs ∙▹ ap g (snd f)) ◃∎ ∎ₛ

⊙compose-pt : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y)
  → app= (de⊙-seq-⊙compose fs) (pt X) ◃∙
    snd (⊙compose fs) ◃∎
    =ₛ
    ↯ (pt-seq fs) ◃∎
⊙compose-pt ⊙idf-seq = =ₛ-in idp
⊙compose-pt {_} {X} {Y} (f ◃⊙∘ fs) =
  app= (de⊙-seq-⊙compose (f ◃⊙∘ fs)) (pt X) ◃∙
  snd (f ⊙∘ ⊙compose fs) ◃∎
    =ₛ⟨ 1 & 1 & expand (ap (fst f) (snd (⊙compose fs)) ◃∙ snd f ◃∎) ⟩
  app= (de⊙-seq-⊙compose (f ◃⊙∘ fs)) (pt X) ◃∙
  ap (fst f) (snd (⊙compose fs)) ◃∙
  snd f ◃∎
    =ₛ₁⟨ 0 & 1 & ∘-ap (_$ pt X) (fst f ∘_) (de⊙-seq-⊙compose fs) ∙
                 ap-∘ (fst f) (_$ pt X) (de⊙-seq-⊙compose fs) ⟩
  ap (fst f) (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
  ap (fst f) (snd (⊙compose fs)) ◃∙
  snd f ◃∎
    =ₛ⟨ 0 & 2 & ⊙compose-pt' (fst f) fs ⟩
  ↯ (pt-seq' (fst f) fs) ◃∙
  snd f ◃∎
    =ₛ₁⟨ ! (↯-∙∙ (pt-seq' (fst f) fs) (snd f ◃∎)) ⟩
  ↯ (pt-seq' (fst f) fs ∙∙ snd f ◃∎) ◃∎ ∎ₛ

record _=∘_ {i} {A B : Type i} (fs gs : A –→ B) : Type i where
  constructor =∘-in
  field
    =∘-out : compose fs == compose gs
open _=∘_ public

abstract
  de⊙-seq-=⊙∘ : ∀ {i} {X Y : Ptd i} {fs gs : X ⊙–→ Y}
    → fs =⊙∘ gs
    → de⊙-seq fs =∘ de⊙-seq gs
  de⊙-seq-=⊙∘ {fs = fs} {gs = gs} p = =∘-in $
    compose (de⊙-seq fs)
      =⟨ de⊙-seq-⊙compose fs ⟩
    fst (⊙compose fs)
      =⟨ ap fst (=⊙∘-out p) ⟩
    fst (⊙compose gs)
      =⟨ ! (de⊙-seq-⊙compose gs) ⟩
    compose (de⊙-seq gs) =∎

  ⊙seq-λ= : ∀ {i} {X Y : Ptd i} {fs gs : X ⊙–→ Y}
    → (p : compose (de⊙-seq fs) ∼ compose (de⊙-seq gs))
    → pt-seq fs =ₛ p (pt X) ◃∙ pt-seq gs
    → fs =⊙∘ gs
  ⊙seq-λ= {_} {X} {Y} {fs} {gs} p q =
    =⊙∘-in $
    pair= (! (de⊙-seq-⊙compose fs) ∙ λ= p ∙ de⊙-seq-⊙compose gs) $
    ↓-app=cst-in $ =ₛ-out $
    snd (⊙compose fs) ◃∎
      =ₛ⟨ pre-rotate-in (⊙compose-pt fs) ⟩
    ! (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    ↯ (pt-seq fs) ◃∎
      =ₛ₁⟨ 1 & 1 & =ₛ-out q ⟩
    ! (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    ↯ (p (pt X) ◃∙ pt-seq gs) ◃∎
      =ₛ⟨ 1 & 1 & =ₛ-in {t = p (pt X) ◃∙ ↯ (pt-seq gs) ◃∎} $
                  ↯-∙∙ (p (pt X) ◃∎) (pt-seq gs) ⟩
    ! (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    p (pt X) ◃∙
    ↯ (pt-seq gs) ◃∎
      =ₛ⟨ 2 & 1 & !ₛ (⊙compose-pt gs) ⟩
    ! (app= (de⊙-seq-⊙compose fs) (pt X)) ◃∙
    p (pt X) ◃∙
    app= (de⊙-seq-⊙compose gs) (pt X) ◃∙
    snd (⊙compose gs) ◃∎
      =ₛ₁⟨ 0 & 1 & !-ap (_$ pt X) (de⊙-seq-⊙compose fs) ⟩
    app= (! (de⊙-seq-⊙compose fs)) (pt X) ◃∙
    p (pt X) ◃∙
    app= (de⊙-seq-⊙compose gs) (pt X) ◃∙
    snd (⊙compose gs) ◃∎
      =ₛ₁⟨ 1 & 1 & ! (app=-β p (pt X)) ⟩
    app= (! (de⊙-seq-⊙compose fs)) (pt X) ◃∙
    app= (λ= p) (pt X) ◃∙
    app= (de⊙-seq-⊙compose gs) (pt X) ◃∙
    snd (⊙compose gs) ◃∎
      =ₛ⟨ 0 & 3 & ∙-ap-seq (_$ pt X) (_ ◃∙ _ ◃∙ _ ◃∎) ⟩
    app= (! (de⊙-seq-⊙compose fs) ∙ λ= p ∙ de⊙-seq-⊙compose gs) (pt X) ◃∙
    snd (⊙compose gs) ◃∎ ∎ₛ

abstract
  !⊙∘ : ∀ {i} {X Y : Ptd i} {fs gs : X ⊙–→ Y} → fs =⊙∘ gs → gs =⊙∘ fs
  !⊙∘ (=⊙∘-in p) = =⊙∘-in (! p)

⊙expand : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) → (⊙compose fs ◃⊙idf) =⊙∘ fs
⊙expand fs = =⊙∘-in idp

⊙contract : ∀ {i} {X Y : Ptd i} {fs : X ⊙–→ Y} → fs =⊙∘ (⊙compose fs ◃⊙idf)
⊙contract = =⊙∘-in idp

private
  _∙⊙∘_ : ∀ {i} {X Y : Ptd i} {fs gs hs : X ⊙–→ Y} → fs =⊙∘ gs → gs =⊙∘ hs → fs =⊙∘ hs
  _∙⊙∘_ (=⊙∘-in p) (=⊙∘-in q) = =⊙∘-in (p ∙ q)

  point-from-target : ∀ {i} {X Y : Ptd i}
    → ℕ → (X ⊙–→ Y) → Ptd i
  point-from-target {Y = Y} O fs = Y
  point-from-target {Y = Y} (S n) ⊙idf-seq = Y
  point-from-target (S n) (f ◃⊙∘ fs) = point-from-target n fs

  take : ∀ {i} (n : ℕ) {X Y : Ptd i} (fs : X ⊙–→ Y) → point-from-target n fs ⊙–→ Y
  take O s = ⊙idf-seq
  take (S n) ⊙idf-seq = ⊙idf-seq
  take (S n) (f ◃⊙∘ fs) = f ◃⊙∘ take n fs

  drop : ∀ {i} (n : ℕ) {X Y : Ptd i} (fs : X ⊙–→ Y) → X ⊙–→ point-from-target n fs
  drop 0 fs = fs
  drop (S n) ⊙idf-seq = ⊙idf-seq
  drop (S n) (f ◃⊙∘ fs) = drop n fs

  infixr 80 _⊙∘∘_
  _⊙∘∘_ : ∀ {i} {X Y Z : Ptd i} (gs : Y ⊙–→ Z) (fs : X ⊙–→ Y) → (X ⊙–→ Z)
  ⊙idf-seq ⊙∘∘ fs = fs
  (g ◃⊙∘ gs) ⊙∘∘ fs = g ◃⊙∘ (gs ⊙∘∘ fs)

  ⊙compose-⊙∘∘ : ∀ {i} {X Y Z : Ptd i} (gs : Y ⊙–→ Z) (fs : X ⊙–→ Y)
    → ⊙compose (gs ⊙∘∘ fs) == ⊙compose gs ⊙∘ ⊙compose fs
  ⊙compose-⊙∘∘ ⊙idf-seq fs = ! (⊙λ= (⊙∘-unit-l (⊙compose fs)))
  ⊙compose-⊙∘∘ (g ◃⊙∘ gs) fs =
    ap (g ⊙∘_) (⊙compose-⊙∘∘ gs fs) ∙
    ! (⊙λ= (⊙∘-assoc g (⊙compose gs) (⊙compose fs)))

  take-drop-split' : ∀ {i} {X Y : Ptd i} (n : ℕ) (fs : X ⊙–→ Y)
    → fs == take n fs ⊙∘∘ drop n fs
  take-drop-split' O fs = idp
  take-drop-split' (S n) ⊙idf-seq = idp
  take-drop-split' (S n) (f ◃⊙∘ fs) = ap (f ◃⊙∘_) (take-drop-split' n fs)

  take-drop-split : ∀ {i} {X Y : Ptd i} (n : ℕ) (s : X ⊙–→ Y)
    → ⊙compose s ◃⊙idf =⊙∘ ⊙compose (take n s) ◃⊙∘ ⊙compose (drop n s) ◃⊙idf
  take-drop-split n fs = =⊙∘-in $
    ⊙compose fs
      =⟨ ap ⊙compose (take-drop-split' n fs) ⟩
    ⊙compose (take n fs ⊙∘∘ drop n fs)
      =⟨ ⊙compose-⊙∘∘ (take n fs) (drop n fs) ⟩
    ⊙compose (take n fs) ⊙∘ ⊙compose (drop n fs) =∎

abstract
  private
    infixr 10 _⊙compose=⟨_&_&_&_⟩_
    _⊙compose=⟨_&_&_&_⟩_ : ∀ {i} {X Y : Ptd i} {f : X ⊙→ Y}
      → (fs : X ⊙–→ Y)
      → (n : ℕ) (m : ℕ)
      → (gs : point-from-target m (drop n fs) ⊙–→ point-from-target n fs)
      → ⊙compose (take m (drop n fs)) == ⊙compose gs
      → ⊙compose (take n fs ⊙∘∘ gs ⊙∘∘ drop m (drop n fs)) == f
      → ⊙compose fs == f
    _⊙compose=⟨_&_&_&_⟩_ {f = f} fs n m gs p p' =
      ⊙compose fs
        =⟨ =⊙∘-out (take-drop-split n fs) ⟩
      ⊙compose (take n fs) ⊙∘ ⊙compose (drop n fs)
        =⟨ ap (⊙compose (take n fs) ⊙∘_) (=⊙∘-out (take-drop-split m (drop n fs))) ⟩
      ⊙compose (take n fs) ⊙∘ ⊙compose (take m (drop n fs)) ⊙∘ ⊙compose (drop m (drop n fs))
        =⟨ ap (λ v → ⊙compose (take n fs) ⊙∘ v ⊙∘ ⊙compose (drop m (drop n fs))) p ⟩
      ⊙compose (take n fs) ⊙∘ ⊙compose gs ⊙∘ ⊙compose (drop m (drop n fs))
        =⟨ ap (⊙compose (take n fs) ⊙∘_) (! (⊙compose-⊙∘∘ gs (drop m (drop n fs)))) ⟩
      ⊙compose (take n fs) ⊙∘ ⊙compose (gs ⊙∘∘ drop m (drop n fs))
        =⟨ ! (⊙compose-⊙∘∘ (take n fs) (gs ⊙∘∘ drop m (drop n fs))) ⟩
      ⊙compose (take n fs ⊙∘∘ gs ⊙∘∘ drop m (drop n fs))
        =⟨ p' ⟩
      f =∎

  infixr 10 _=⊙∘⟨_⟩_
  _=⊙∘⟨_⟩_ : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) {gs hs : X ⊙–→ Y}
    → fs =⊙∘ gs
    → gs =⊙∘ hs
    → fs =⊙∘ hs
  _=⊙∘⟨_⟩_ _ p q = p ∙⊙∘ q

  infixr 10 _=⊙∘⟨_&_&_⟩_
  _=⊙∘⟨_&_&_⟩_ : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) {gs : X ⊙–→ Y}
    → (m n : ℕ)
    → {hs : point-from-target n (drop m fs) ⊙–→ point-from-target m fs}
    → take n (drop m fs) =⊙∘ hs
    → take m fs ⊙∘∘ hs ⊙∘∘ drop n (drop m fs) =⊙∘ gs
    → fs =⊙∘ gs
  _=⊙∘⟨_&_&_⟩_ fs m n {hs} p p' = =⊙∘-in (fs ⊙compose=⟨ m & n & hs & =⊙∘-out p ⟩ =⊙∘-out p')

  infixr 10 _=⊙∘₁⟨_⟩_
  _=⊙∘₁⟨_⟩_ : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) {gs : X ⊙–→ Y}
    → {h : X ⊙→ Y}
    → ⊙compose fs == h
    → h ◃⊙idf =⊙∘ gs
    → fs =⊙∘ gs
  _=⊙∘₁⟨_⟩_ fs p p' = =⊙∘-in p ∙⊙∘ p'

  infixr 10 _=⊙∘₁⟨_&_&_⟩_
  _=⊙∘₁⟨_&_&_⟩_ : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) {gs : X ⊙–→ Y}
    → (m n : ℕ)
    → {h : point-from-target n (drop m fs) ⊙→ point-from-target m fs}
    → ⊙compose (take n (drop m fs)) == h
    → take m fs ⊙∘∘ h ◃⊙∘ drop n (drop m fs) =⊙∘ gs
    → fs =⊙∘ gs
  _=⊙∘₁⟨_&_&_⟩_ fs m n {h} p p' = fs =⊙∘⟨ m & n & (=⊙∘-in {gs = h ◃⊙idf} p) ⟩ p'

infix 15 _∎⊙∘
_∎⊙∘ : ∀ {i} {X Y : Ptd i} (fs : X ⊙–→ Y) → fs =⊙∘ fs
_∎⊙∘ _ = =⊙∘-in idp

⊙coe-seq : ∀ {i} {X Y : Ptd i}
  → X =-= Y
  → X ⊙–→ Y
⊙coe-seq [] = ⊙idf-seq
⊙coe-seq (p ◃∙ ps) = ⊙coe-seq ps ⊙∘∘ ⊙coe p ◃⊙idf

⊙coe-seq-∙ : ∀ {i} {X Y : Ptd i} (ps : X =-= Y)
  → ⊙coe (↯ ps) ◃⊙idf =⊙∘ ⊙coe-seq ps
⊙coe-seq-∙ [] = =⊙∘-in idp
⊙coe-seq-∙ (p ◃∙ ps) =
  ⊙coe (↯ (p ◃∙ ps)) ◃⊙idf
    =⊙∘₁⟨ ap ⊙coe (↯-∙∙ (p ◃∎) ps) ⟩
  ⊙coe (p ∙ ↯ ps) ◃⊙idf
    =⊙∘⟨ ⊙coe-∙ p (↯ ps) ⟩
  ⊙coe (↯ ps) ◃⊙∘ ⊙coe p ◃⊙idf
    =⊙∘⟨ 0 & 1 & ⊙coe-seq-∙ ps ⟩
  ⊙coe-seq ps ⊙∘∘ ⊙coe p ◃⊙idf ∎⊙∘

⊙coe-seq-=ₛ : ∀ {i} {X Y : Ptd i} {ps qs : X =-= Y}
  → ps =ₛ qs
  → ⊙coe-seq ps =⊙∘ ⊙coe-seq qs
⊙coe-seq-=ₛ {ps = ps} {qs = qs} r =
  ⊙coe-seq ps
    =⊙∘⟨ !⊙∘ (⊙coe-seq-∙ ps) ⟩
  ⊙coe (↯ ps) ◃⊙idf
    =⊙∘₁⟨ ap ⊙coe (=ₛ-out r) ⟩
  ⊙coe (↯ qs) ◃⊙idf
    =⊙∘⟨ ⊙coe-seq-∙ qs ⟩
  ⊙coe-seq qs ∎⊙∘
