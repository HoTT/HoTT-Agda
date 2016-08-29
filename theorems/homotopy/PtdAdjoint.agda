{-# OPTIONS --without-K #-}

open import HoTT

{- The pseudo-adjoint functors F,G : Ptd → Ptd
 - It stops at composition and ignores
 - all the higher associahedrons.
 -}

module homotopy.PtdAdjoint where

record PtdFunctor i j : Type (lsucc (lmax i j)) where
  field
    obj : Ptd i → Ptd j
    arr : {X Y : Ptd i} → fst (X ⊙→ Y) → fst (obj X ⊙→ obj Y)
    id : (X : Ptd i) → arr (⊙idf X) == ⊙idf (obj X)
    comp : {X Y Z : Ptd i} (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → arr (g ⊙∘ f) == arr g ⊙∘ arr f

{- counit-unit description of F ⊣ G -}
record CounitUnitAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G

  field
    η : (X : Ptd i) → fst (X ⊙→ G.obj (F.obj X))
    ε : (U : Ptd j) → fst (F.obj (G.obj U) ⊙→ U)

    η-natural : {X Y : Ptd i} (h : fst (X ⊙→ Y))
      → η Y ⊙∘ h == G.arr (F.arr h) ⊙∘ η X
    ε-natural : {U V : Ptd j} (k : fst (U ⊙→ V))
      → ε V ⊙∘ F.arr (G.arr k) == k ⊙∘ ε U

    εF-Fη : (X : Ptd i) → ε (F.obj X) ⊙∘ F.arr (η X) == ⊙idf (F.obj X)
    Gε-ηG : (U : Ptd j) → G.arr (ε U) ⊙∘ η (G.obj U) == ⊙idf (G.obj U)

{- hom-set isomorphism description of F ⊣ G -}
record HomAdjoint {i j} (F : PtdFunctor i j) (G : PtdFunctor j i)
  : Type (lsucc (lmax i j)) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G

  field
    eq : (X : Ptd i) (U : Ptd j) → fst (F.obj X ⊙→ U) ≃ fst (X ⊙→ G.obj U)

    nat-dom : {X Y : Ptd i} (h : fst (X ⊙→ Y)) (U : Ptd j)
      (r : fst (F.obj Y ⊙→ U))
      → –> (eq Y U) r ⊙∘ h == –> (eq X U) (r ⊙∘ F.arr h)

    nat-cod : (X : Ptd i) {U V : Ptd j} (k : fst (U ⊙→ V))
      (r : fst (F.obj X ⊙→ U))
      → G.arr k ⊙∘ –> (eq X U) r == –> (eq X V) (k ⊙∘ r)

  nat!-dom : {X Y : Ptd i} (h : fst (X ⊙→ Y)) (U : Ptd j)
    (s : fst (Y ⊙→ G.obj U))
    → <– (eq Y U) s ⊙∘ F.arr h == <– (eq X U) (s ⊙∘ h)
  nat!-dom {X} {Y} h U s =
    ! (<–-inv-l (eq X U) (<– (eq Y U) s ⊙∘ F.arr h))
    ∙ ap (<– (eq X U)) (! (nat-dom h U (<– (eq Y U) s)))
    ∙ ap (λ w → <– (eq X U) (w ⊙∘ h)) (<–-inv-r (eq Y U) s)

  nat!-cod : (X : Ptd i) {U V : Ptd j} (k : fst (U ⊙→ V))
    (s : fst (X ⊙→ G.obj U))
    → k ⊙∘ <– (eq X U) s == <– (eq X V) (G.arr k ⊙∘ s)
  nat!-cod X {U} {V} k s =
    ! (<–-inv-l (eq X V) (k ⊙∘ <– (eq X U) s))
    ∙ ap (<– (eq X V)) (! (nat-cod X k (<– (eq X U) s)))
    ∙ ap (λ w → <– (eq X V) (G.arr k ⊙∘ w)) (<–-inv-r (eq X U) s)

counit-unit-to-hom : ∀ {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  → CounitUnitAdjoint F G → HomAdjoint F G
counit-unit-to-hom {i} {j} {F} {G} adj = record {
  eq = eq;
  nat-dom = nat-dom;
  nat-cod = nat-cod}
  where
  module F = PtdFunctor F
  module G = PtdFunctor G
  open CounitUnitAdjoint adj

  module _ (X : Ptd i) (U : Ptd j) where

    into : fst (F.obj X ⊙→ U) → fst (X ⊙→ G.obj U)
    into r = G.arr r ⊙∘ η X

    out : fst (X ⊙→ G.obj U) → fst (F.obj X ⊙→ U)
    out s = ε U ⊙∘ F.arr s

    into-out : (s : fst (X ⊙→ G.obj U)) → into (out s) == s
    into-out s =
      G.arr (ε U ⊙∘ F.arr s) ⊙∘ η X
        =⟨ G.comp (ε U) (F.arr s) |in-ctx (λ w → w ⊙∘ η X) ⟩
      (G.arr (ε U) ⊙∘ G.arr (F.arr s)) ⊙∘ η X
        =⟨ ⊙∘-assoc (G.arr (ε U)) (G.arr (F.arr s)) (η X) ⟩
      G.arr (ε U) ⊙∘ G.arr (F.arr s) ⊙∘ η X
        =⟨ ! (η-natural s) |in-ctx (λ w → G.arr (ε U) ⊙∘ w) ⟩
      G.arr (ε U) ⊙∘ η (G.obj U) ⊙∘ s
        =⟨ ! (⊙∘-assoc (G.arr (ε U)) (η (G.obj U)) s) ⟩
      (G.arr (ε U) ⊙∘ η (G.obj U)) ⊙∘ s
        =⟨ Gε-ηG U |in-ctx (λ w → w ⊙∘ s) ⟩
      ⊙idf (G.obj U) ⊙∘ s
        =⟨ ⊙∘-unit-l s ⟩
      s ∎

    out-into : (r : fst (F.obj X ⊙→ U)) → out (into r) == r
    out-into r =
      ε U ⊙∘ F.arr (G.arr r ⊙∘ η X)
        =⟨ F.comp (G.arr r) (η X) |in-ctx (λ w → ε U ⊙∘ w) ⟩
      ε U ⊙∘ F.arr (G.arr r) ⊙∘ F.arr (η X)
        =⟨ ! (⊙∘-assoc (ε U) (F.arr (G.arr r)) (F.arr (η X))) ⟩
      (ε U ⊙∘ F.arr (G.arr r)) ⊙∘ F.arr (η X)
        =⟨ ε-natural r |in-ctx (λ w → w ⊙∘ F.arr (η X)) ⟩
      (r ⊙∘ ε (F.obj X)) ⊙∘ F.arr (η X)
        =⟨ ⊙∘-assoc r (ε (F.obj X)) (F.arr (η X)) ⟩
      r ⊙∘ ε (F.obj X) ⊙∘ F.arr (η X)
        =⟨ εF-Fη X |in-ctx (λ w → r ⊙∘ w) ⟩
      r ∎

    eq : fst (F.obj X ⊙→ U) ≃ fst (X ⊙→ G.obj U)
    eq = equiv into out into-out out-into

  nat-dom : {X Y : Ptd i} (h : fst (X ⊙→ Y)) (U : Ptd j)
    (r : fst (F.obj Y ⊙→ U))
    → –> (eq Y U) r ⊙∘ h == –> (eq X U) (r ⊙∘ F.arr h)
  nat-dom {X} {Y} h U r =
    (G.arr r ⊙∘ η Y) ⊙∘ h
      =⟨ ⊙∘-assoc (G.arr r) (η Y) h ⟩
    G.arr r ⊙∘ η Y ⊙∘ h
      =⟨ η-natural h |in-ctx (λ w → G.arr r ⊙∘ w) ⟩
    G.arr r ⊙∘ G.arr (F.arr h) ⊙∘ η X
      =⟨ ! (⊙∘-assoc (G.arr r) (G.arr (F.arr h)) (η X)) ⟩
    (G.arr r ⊙∘ G.arr (F.arr h)) ⊙∘ η X
      =⟨ ! (G.comp r (F.arr h)) |in-ctx (λ w → w ⊙∘ η X) ⟩
    G.arr (r ⊙∘ F.arr h) ⊙∘ η X ∎

  nat-cod : (X : Ptd i) {U V : Ptd j} (k : fst (U ⊙→ V))
    (r : fst (F.obj X ⊙→ U))
    → G.arr k ⊙∘ –> (eq X U) r == –> (eq X V) (k ⊙∘ r)
  nat-cod X k r =
    G.arr k ⊙∘ (G.arr r ⊙∘ η X)
      =⟨ ! (⊙∘-assoc (G.arr k) (G.arr r) (η X)) ⟩
    (G.arr k ⊙∘ G.arr r) ⊙∘ η X
      =⟨ ! (G.comp k r) |in-ctx (λ w → w ⊙∘ η X) ⟩
    G.arr (k ⊙∘ r) ⊙∘ η X ∎

{- a right adjoint preserves products -}
module RightAdjoint× {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G) (U V : Ptd j) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G
    module A = HomAdjoint adj

  ⊙into : fst (G.obj (U ⊙× V) ⊙→ G.obj U ⊙× G.obj V)
  ⊙into = ⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)

  ⊙out : fst (G.obj U ⊙× G.obj V ⊙→ G.obj (U ⊙× V))
  ⊙out = –> (A.eq _ _) (⊙fanout (<– (A.eq _ _) ⊙fst)
                                (<– (A.eq _ _) ⊙snd))

  ⊙into-out : ⊙into ⊙∘ ⊙out == ⊙idf _
  ⊙into-out =
    ⊙fanout (G.arr ⊙fst) (G.arr ⊙snd) ⊙∘ ⊙out
      =⟨ ⊙fanout-pre∘ (G.arr ⊙fst) (G.arr ⊙snd) ⊙out ⟩
    ⊙fanout (G.arr ⊙fst ⊙∘ ⊙out) (G.arr ⊙snd ⊙∘ ⊙out)
      =⟨ ap2 ⊙fanout
           (A.nat-cod _ ⊙fst (⊙fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd))
            ∙ ap (–> (A.eq _ _))
                 (⊙fst-fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd))
            ∙ <–-inv-r (A.eq _ _) ⊙fst)
           (A.nat-cod _ ⊙snd (⊙fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd))
            ∙ ap (–> (A.eq _ _))
                 (⊙snd-fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd))
            ∙ <–-inv-r (A.eq _ _) ⊙snd) ⟩
    ⊙fanout ⊙fst ⊙snd ∎

  ⊙out-into : ⊙out ⊙∘ ⊙into == ⊙idf _
  ⊙out-into =
    –> (A.eq _ _) (⊙fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd))
    ⊙∘ ⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)
      =⟨ A.nat-dom (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)) _
           (⊙fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd)) ⟩
    –> (A.eq _ _) (⊙fanout (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd)
    ⊙∘ F.arr (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)))
      =⟨ ⊙fanout-pre∘ (<– (A.eq _ _) ⊙fst) (<– (A.eq _ _) ⊙snd)
           (F.arr (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)))
         |in-ctx –> (A.eq _ _) ⟩
    –> (A.eq _ _) (⊙fanout
            (<– (A.eq _ _) ⊙fst ⊙∘ F.arr (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)))
            (<– (A.eq _ _) ⊙snd ⊙∘ F.arr (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd))))
      =⟨ ap2 (λ f g → –> (A.eq _ _) (⊙fanout f g))
           (A.nat!-dom (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)) _ ⊙fst
            ∙ ap (<– (A.eq _ _)) (⊙fst-fanout (G.arr ⊙fst) (G.arr ⊙snd))
            ∙ ! (A.nat!-cod _ ⊙fst (⊙idf _)))
           (A.nat!-dom (⊙fanout (G.arr ⊙fst) (G.arr ⊙snd)) _ ⊙snd
            ∙ ap (<– (A.eq _ _)) (⊙snd-fanout (G.arr ⊙fst) (G.arr ⊙snd))
            ∙ ! (A.nat!-cod _ ⊙snd (⊙idf _))) ⟩
    –> (A.eq _ _) (⊙fanout (⊙fst ⊙∘ <– (A.eq _ _) (⊙idf _))
                           (⊙snd ⊙∘ <– (A.eq _ _) (⊙idf _)))
      =⟨ ap (–> (A.eq _ _)) (! (⊙fanout-pre∘ ⊙fst ⊙snd (<– (A.eq _ _) (⊙idf _)))) ⟩
    –> (A.eq _ _) (⊙fanout ⊙fst ⊙snd ⊙∘ <– (A.eq _ _) (⊙idf _))
      =⟨ ⊙∘-unit-l _ |in-ctx –> (A.eq _ _) ⟩
    –> (A.eq _ _) (<– (A.eq _ _) (⊙idf _))
      =⟨ <–-inv-r (A.eq _ _) (⊙idf _) ⟩
    ⊙idf _ ∎

  ⊙eq : G.obj (U ⊙× V) ⊙≃ G.obj U ⊙× G.obj V
  ⊙eq = ≃-to-⊙≃ (equiv (fst ⊙into) (fst ⊙out)
                  (app= (ap fst ⊙into-out)) (app= (ap fst ⊙out-into)))
                (snd ⊙into)

  ⊙path = ⊙ua ⊙eq

{- Using the equivalence in RightAdjoint× we get a binary
 - "G.arr2" : (X × Y → Z) → (G X × G Y → G Z)
 - and there is some kind of naturality wrt the (FX→Y)≃(X→GY) equivalence
 - (use case: from ⊙ap we get ⊙ap2) -}
module RightAdjointBinary {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G)
  where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G
    module A = HomAdjoint adj
    module A× = RightAdjoint× adj

  arr2 : {X Y Z : Ptd j}
    → fst (X ⊙× Y ⊙→ Z) → fst (G.obj X ⊙× G.obj Y ⊙→ G.obj Z)
  arr2 {X} {Y} {Z} f = G.arr f ⊙∘ A×.⊙out X Y

  nat-cod : {X : Ptd i} {Y Z W : Ptd j}
    (r₁ : fst (F.obj X ⊙→ Y)) (r₂ : fst (F.obj X ⊙→ Z))
    (o : fst (Y ⊙× Z ⊙→ W))
    → –> (A.eq X W) (o ⊙∘ ⊙fanout r₁ r₂)
      == arr2 o ⊙∘ ⊙fanout (–> (A.eq X Y) r₁) (–> (A.eq X Z) r₂)
  nat-cod {X} {Y} {Z} {W} r₁ r₂ o =
    –> (A.eq X W) (o ⊙∘ ⊙fanout r₁ r₂)
      =⟨ ! (A.nat-cod X o (⊙fanout r₁ r₂)) ⟩
    G.arr o ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ! (A×.⊙out-into Y Z)
         |in-ctx (λ w → (G.arr o ⊙∘ w) ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)) ⟩
    (G.arr o ⊙∘ (A×.⊙out Y Z ⊙∘ A×.⊙into Y Z))
    ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ⊙∘-assoc-lemma (G.arr o) (A×.⊙out Y Z) (A×.⊙into Y Z)
           (–> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)) ⟩
    arr2 o ⊙∘ A×.⊙into Y Z ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂)
      =⟨ ⊙fanout-pre∘ (G.arr ⊙fst) (G.arr ⊙snd) (–> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
         |in-ctx (λ w → arr2 o ⊙∘ w) ⟩
    arr2 o ⊙∘ ⊙fanout (G.arr ⊙fst ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
                      (G.arr ⊙snd ⊙∘ –> (A.eq X (Y ⊙× Z)) (⊙fanout r₁ r₂))
      =⟨ ap2 (λ w₁ w₂ → arr2 o ⊙∘ ⊙fanout w₁ w₂)
           (A.nat-cod X ⊙fst (⊙fanout r₁ r₂)
            ∙ ap (–> (A.eq X Y)) (⊙fst-fanout r₁ r₂))
           (A.nat-cod X ⊙snd (⊙fanout r₁ r₂)
            ∙ ap (–> (A.eq X Z)) (⊙snd-fanout r₁ r₂)) ⟩
    arr2 o ⊙∘ ⊙fanout (–> (A.eq X Y) r₁) (–> (A.eq X Z) r₂) ∎
    where
    ⊙∘-assoc-lemma : ∀ {i j k l m}
      {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {U : Ptd l} {V : Ptd m}
      (k : fst (U ⊙→ V)) (h : fst (Z ⊙→ U))
      (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
      → (k ⊙∘ (h ⊙∘ g)) ⊙∘ f == (k ⊙∘ h) ⊙∘ g ⊙∘ f
    ⊙∘-assoc-lemma (k , idp) (h , idp) (g , idp) (f , idp) = idp

{- a left adjoint preserves wedges -}
module LeftAdjoint∨ {i j} {F : PtdFunctor i j} {G : PtdFunctor j i}
  (adj : HomAdjoint F G) (U V : Ptd i) where

  private
    module F = PtdFunctor F
    module G = PtdFunctor G
    module A = HomAdjoint adj

  module Into = ⊙WedgeRec (F.arr ⊙winl) (F.arr ⊙winr)

  ⊙into : fst (F.obj U ⊙∨ F.obj V ⊙→ F.obj (U ⊙∨ V))
  ⊙into = Into.⊙f

  module OutHelp = ⊙WedgeRec (–> (A.eq _ _) ⊙winl) (–> (A.eq _ _) ⊙winr)

  ⊙out : fst (F.obj (U ⊙∨ V) ⊙→ F.obj U ⊙∨ F.obj V)
  ⊙out = <– (A.eq _ _) OutHelp.⊙f

  ⊙into-out : ⊙into ⊙∘ ⊙out == ⊙idf _
  ⊙into-out =
    ⊙into ⊙∘ ⊙out
      =⟨ A.nat!-cod _ ⊙into (⊙Wedge-rec (–> (A.eq _ _) ⊙winl)
                                        (–> (A.eq _ _) ⊙winr)) ⟩
    <– (A.eq _ _) (G.arr ⊙into ⊙∘ ⊙Wedge-rec (–> (A.eq _ _) ⊙winl)
                                             (–> (A.eq _ _) ⊙winr))
      =⟨ ap (<– (A.eq _ _)) (⊙Wedge-rec-post∘ (G.arr ⊙into)
                              (–> (A.eq _ _) ⊙winl) (–> (A.eq _ _) ⊙winr)) ⟩
    <– (A.eq _ _) (⊙Wedge-rec (G.arr ⊙into ⊙∘ –> (A.eq _ _) ⊙winl)
                              (G.arr ⊙into ⊙∘ –> (A.eq _ _) ⊙winr))
      =⟨ ap2 (λ w₁ w₂ → <– (A.eq _ _) (⊙Wedge-rec w₁ w₂))
             (A.nat-cod _ ⊙into ⊙winl
              ∙ ap (–> (A.eq _ _)) (Into.⊙winl-β ∙ ! (⊙∘-unit-l _))
              ∙ ! (A.nat-dom ⊙winl _ (⊙idf _)))
             (A.nat-cod _ ⊙into ⊙winr
              ∙ ap (–> (A.eq _ _)) (Into.⊙winr-β ∙ ! (⊙∘-unit-l _))
              ∙ ! (A.nat-dom ⊙winr _ (⊙idf _))) ⟩
    <– (A.eq _ _) (⊙Wedge-rec (–> (A.eq _ _) (⊙idf _) ⊙∘ ⊙winl)
                              (–> (A.eq _ _) (⊙idf _) ⊙∘ ⊙winr))
      =⟨ ap (<– (A.eq _ _))
            (! (⊙Wedge-rec-post∘ (–> (A.eq _ _) (⊙idf _)) ⊙winl ⊙winr)) ⟩
    <– (A.eq _ _) (–> (A.eq _ _) (⊙idf _) ⊙∘ ⊙Wedge-rec ⊙winl ⊙winr)
      =⟨ ap (λ w → <– (A.eq _ _) (–> (A.eq _ _) (⊙idf _) ⊙∘ w))
            ⊙Wedge-rec-η ⟩
    <– (A.eq _ _) (–> (A.eq _ _) (⊙idf _))
      =⟨ <–-inv-l (A.eq _ _) (⊙idf _) ⟩
    ⊙idf _ ∎

  ⊙out-into : ⊙out ⊙∘ ⊙into == ⊙idf _
  ⊙out-into =
    ⊙out ⊙∘ ⊙Wedge-rec (F.arr ⊙winl) (F.arr ⊙winr)
      =⟨ ⊙Wedge-rec-post∘ ⊙out (F.arr ⊙winl) (F.arr ⊙winr) ⟩
    ⊙Wedge-rec (⊙out ⊙∘ F.arr ⊙winl) (⊙out ⊙∘ F.arr ⊙winr)
      =⟨ ap2 ⊙Wedge-rec
           (A.nat!-dom ⊙winl _ (⊙Wedge-rec _ _)
            ∙ ap (<– (A.eq _ _)) OutHelp.⊙winl-β
            ∙ <–-inv-l (A.eq _ _) ⊙winl)
           (A.nat!-dom ⊙winr _ (⊙Wedge-rec _ _)
            ∙ ap (<– (A.eq _ _)) OutHelp.⊙winr-β
            ∙ <–-inv-l (A.eq _ _) ⊙winr) ⟩
    ⊙Wedge-rec ⊙winl ⊙winr
      =⟨ ⊙Wedge-rec-η ⟩
    ⊙idf _ ∎

  ⊙eq : F.obj U ⊙∨ F.obj V ⊙≃ F.obj (U ⊙∨ V)
  ⊙eq = ≃-to-⊙≃ (equiv (fst ⊙into) (fst ⊙out)
                  (app= (ap fst ⊙into-out)) (app= (ap fst ⊙out-into)))
                (snd ⊙into)

  ⊙path = ⊙ua ⊙eq
