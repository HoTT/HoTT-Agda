{-# OPTIONS --without-K #-}

open import homotopy.3x3.Common
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose

module homotopy.JoinAssoc3x3 {i} (A B C : Type i) where

open M using (Pushout^2)

join-assoc-span^2 : Span^2 {i}
join-assoc-span^2 =
  span^2 A (A × C) (A × C) (A × B) ((A × B) × C) (A × C) B (B × C) C
         fst (idf _) fst (λ u → fst (fst u) , snd u) fst snd fst snd (λ u → fst (fst u) , snd u) (λ u → snd (fst u) , snd u) (idf _) snd
         (λ _ → idp) (λ _ → idp) (λ _ → idp) (λ _ → idp)

open import homotopy.3x3.Commutes join-assoc-span^2 as PP

module _ (A B : Type i) (f : B → A) where

  lemma3-fun : Pushout (span A B B f (idf _)) → A
  lemma3-fun = Lemma3Fun.f  module _ where

    module Lemma3Fun = PushoutRec {d = span A B B f (idf _)} (idf _) f (λ _ → idp)

  lemma3-eq : (x : Pushout (span A B B f (idf _))) → left (lemma3-fun x) == x
  lemma3-eq = Pushout-elim (λ _ → idp) glue (λ b → ↓-∘=idf-in' left lemma3-fun (idp,=□idp,-in idp ∙□-i/ idp / ! (ap (ap left) (Lemma3Fun.glue-β b)) /))

  lemma3 : Pushout (span A B B f (idf _)) ≃ A
  lemma3 = equiv lemma3-fun left (λ _ → idp) lemma3-eq

module _ (A B : Type i) (f : B → A) where

  lemma3'-fun : Pushout (span B A B (idf _) f) → A
  lemma3'-fun = Lemma3'Fun.f  module _ where

    module Lemma3'Fun = PushoutRec {d = span B A B (idf _) f} f (idf _) (λ _ → idp)

  lemma3'-eq : (x : Pushout (span B A B (idf _) f)) → right (lemma3'-fun x) == x
  lemma3'-eq = ! ∘ (Pushout-elim glue (λ _ → idp) (λ b → ↓-idf=∘-in right lemma3'-fun (,idp=□,idp-in idp ∙□-i/ ap (ap right) (Lemma3'Fun.glue-β b) / idp /)))

  lemma3' : Pushout (span B A B (idf _) f) ≃ A
  lemma3' = equiv lemma3'-fun right (λ _ → idp) lemma3'-eq

module _ (X Y Z T : Type i) (f : Z → X) (g : Z → Y) where

  private
    P1 : Type i
    P1 = Pushout (span X Y Z f g)

    P2 : Type i
    P2 = Pushout (span (X × T) (Y × T) (Z × T) (λ u → (f (fst u) , snd u)) (λ u → (g (fst u) , snd u)))

  lemma4 : P2 ≃ (P1 × T)
  lemma4 = equiv to from to-from from-to  module Lemma4 where

    to : P2 → P1 × T
    to = To.f  module _ where

      module To = PushoutRec (λ u → (left (fst u) , snd u)) (λ u → (right (fst u) , snd u)) (λ u → pair×= (glue (fst u)) idp)

    from-curr : T → (P1 → P2)
    from-curr t = FromCurr.f  module _ where

      module FromCurr = PushoutRec {D = P2} (λ x → left (x , t)) (λ y → right (y , t)) (λ z → glue (z , t))

    from : P1 × T → P2
    from (x , t) = from-curr t x

    to-from : (u : P1 × T) → to (from u) == u
    to-from (x , t) = to-from-curr t x  where

      ap-idf,×cst : ∀ {i j} {A : Type i} {B : Type j}
        {x y : A} (p : x == y) {b : B}
        → ap (λ v → v , b) p == pair×= p idp
      ap-idf,×cst idp = idp

      to-from-curr : (t : T) (x : P1) → to (from-curr t x) == (x , t)
      to-from-curr t = Pushout-elim (λ _ → idp) (λ _ → idp) (λ z → ↓-='-in' (ap-idf,×cst (glue z) ∙ ! (To.glue-β (z , t)) ∙ ! (ap (ap to) (FromCurr.glue-β t z)) ∙ ∘-ap to (from-curr t) (glue z)))

    from-to : (u : P2) → from (to u) == u
    from-to = Pushout-elim (λ _ → idp) (λ _ → idp) (λ c → ↓-∘=idf-in' from to (! (ap (ap from) (To.glue-β c) ∙ ap-pair×= from (glue (fst c)) ∙ FromCurr.glue-β (snd c) (fst c))))  where

      ap-pair×= : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
        {a a' : A} (p : a == a') {b : B}
        → ap f (pair×= p idp) == ap (λ a → f (a , b)) p
      ap-pair×= f {a = a} {a' = .a} idp = idp

module _ (X Y T : Type i) where

  private
    P1 : Type i
    P1 = Pushout (span X Y (X × Y) fst snd)

    P2 : Type i
    P2 = Pushout (span (T × X) (T × Y) ((T × X) × Y) fst (λ u → (fst (fst u) , snd u)))

  lemma4' : P2 ≃ (T × P1)
  lemma4' = equiv to from to-from from-to  module Lemma4' where

    to : P2 → T × P1
    to = To.f  module _ where

      module To = PushoutRec {D = T × P1} (λ u → (fst u , left (snd u))) (λ u → (fst u , right (snd u))) (λ c → pair×= idp (glue (snd (fst c) , snd c)))

    from-curr : T → (P1 → P2)
    from-curr t = FromCurr.f  module _ where

      module FromCurr = PushoutRec {D = P2} (λ x → left (t , x)) (λ y → right (t , y)) (λ z → glue ((t , fst z) , snd z))

    from : T × P1 → P2
    from (t , x) = from-curr t x

    to-from : (u : T × P1) → to (from u) == u
    to-from (t , x) = to-from-curr t x  where

      to-from-curr : (t : T) (x : P1) → to (from-curr t x) == (t , x)
      to-from-curr t = Pushout-elim (λ _ → idp) (λ _ → idp) (λ c → ↓-='-in' (ap-cst,id (λ _ → _) (glue c) ∙ ! (lemma5 c)))  where

        lemma5 : (c : X × Y) → ap (to ∘ from-curr t) (glue c) == pair×= idp (glue c)
        lemma5 (x , y) =
          ap (to ∘ from-curr t) (glue (x , y))
            =⟨ ap-∘ to (from-curr t) (glue (x , y)) ⟩
          ap to (ap (from-curr t) (glue (x , y)))
            =⟨ FromCurr.glue-β t (x , y) |in-ctx ap to ⟩
          ap to (glue ((t , x) , y))
            =⟨ To.glue-β ((t , x) , y) ⟩
          pair×= idp (glue (x , y)) ∎

    from-to : (x : P2) → from (to x) == x
    from-to = Pushout-elim (λ _ → idp) (λ _ → idp) (λ c → ↓-∘=idf-in' from to (! (lemma42 c)))  where

      ap-pair×= : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A × B → C)
        {a : A} {b b' : B} (p : b == b')
        → ap f (pair×= idp p) == ap (λ b → f (a , b)) p
      ap-pair×= f {b = b} {b' = .b} idp = idp

      lemma42 : (c : (T × X) × Y) → ap from (ap to (glue c)) == glue c
      lemma42 ((t , x) , y) =
        ap from (ap to (glue ((t , x) , y)))
          =⟨ To.glue-β ((t , x) , y) |in-ctx ap from ⟩
        ap from (pair×= idp (glue (x , y)))
          =⟨ ap-pair×= from (glue (x , y)) ⟩
        ap (from-curr t) (glue (x , y))
          =⟨ FromCurr.glue-β t (x , y) ⟩
        glue ((t , x) , y) ∎

lemma2 : M.v-h-span join-assoc-span^2 == *-span A (B * C)
lemma2 = span= (lemma3 A (A × C) fst) (ide _) (lemma4' B C A)
               (Pushout-elim (λ _ → idp) (λ _ → idp) (λ x → ↓-='-in' (lemma2-1 x ∙ ! (lemma2-2 x))))
               (Pushout-elim (λ _ → idp) (λ _ → idp) (λ x → ↓-='-in' (lemma2-3 x ∙ ! (M.F₃∙.glue-β join-assoc-span^2 _ ∙ ∙-unit-r (glue _))))) where

  lemma2-1 : (x : (A × B) × C) → _
  lemma2-1 ((a , b) , c) =
    ap (fst ∘ Lemma4'.to B C A) (glue ((a , b) , c))
      =⟨ ap-∘ fst (Lemma4'.to B C A) (glue ((a , b) , c)) ⟩
    ap fst (ap (Lemma4'.to B C A) (glue ((a , b) , c)))
      =⟨ Lemma4'.To.glue-β B C A ((a , b) , c) |in-ctx fst×= ⟩
    fst×= (pair×= idp (glue (b , c)))
      =⟨ fst×=-β idp (glue (b , c)) ⟩
    idp ∎

  lemma2-2 : (x : (A × B) × C) → _
  lemma2-2 ((a , b) , c) =
    ap (lemma3-fun A (A × C) fst ∘ M.f₁∙ join-assoc-span^2) (glue ((a , b) , c))
      =⟨ ap-∘ (lemma3-fun A (A × C) fst) (M.f₁∙ join-assoc-span^2) (glue ((a , b) , c)) ⟩
    ap (lemma3-fun A (A × C) fst) (ap (M.f₁∙ join-assoc-span^2) (glue ((a , b) , c)))
      =⟨ M.F₁∙.glue-β join-assoc-span^2 ((a , b) , c) |in-ctx ap (lemma3-fun A (A × C) fst) ⟩
    ap (lemma3-fun A (A × C) fst) (glue (a , c) ∙ idp)
      =⟨ ∙-unit-r (glue (a , c)) |in-ctx ap (lemma3-fun A (A × C) fst) ⟩
    ap (lemma3-fun A (A × C) fst) (glue (a , c))
      =⟨ Lemma3Fun.glue-β A (A × C) fst (a , c) ⟩
    idp ∎

  lemma2-3 : (x : (A × B) × C) → _
  lemma2-3 ((a , b) , c) =
    ap (snd ∘ Lemma4'.to B C A) (glue ((a , b) , c))
      =⟨ ap-∘ snd (Lemma4'.to B C A) (glue ((a , b) , c)) ⟩
    ap snd (ap (Lemma4'.to B C A) (glue ((a , b) , c)))
      =⟨ Lemma4'.To.glue-β B C A ((a , b) , c) |in-ctx snd×= ⟩
    snd×= (pair×= idp (glue (b , c)))
      =⟨ snd×=-β idp (glue (b , c)) ⟩
    glue (b , c) ∎

lemma2' : M.v-h-span (transpose join-assoc-span^2) == *-span (A * B) C
lemma2' = span= (ide _) (lemma3' C (A × C) snd) (lemma4 A B (A × B) C fst snd)
          (Pushout-elim (λ _ → idp) (λ _ → idp) (λ c → ↓-='-in' (ap-∘ fst (Lemma4.to A B (A × B) C fst snd) (glue c) ∙ ap (ap fst) (Lemma4.To.glue-β A B (A × B) C fst snd c) ∙ fst×=-β (glue (fst c)) idp ∙ ! (∙-unit-r (glue (fst c))) ∙ ! (M.F₁∙.glue-β (transpose join-assoc-span^2) c))))
          (Pushout-elim (λ _ → idp) (λ _ → idp) (λ u → ↓-='-in' (lemma2'-1 u ∙ ! (lemma2'-2 u))))  where

  lemma2'-1 : (u : (A × B) × C) → ap (snd ∘ Lemma4.to A B (A × B) C fst snd) (glue u) == idp
  lemma2'-1 u =
    ap (snd ∘ Lemma4.to A B (A × B) C fst snd) (glue u)
      =⟨ ap-∘ snd (Lemma4.to A B (A × B) C fst snd) (glue u) ⟩
    ap snd (ap (Lemma4.to A B (A × B) C fst snd) (glue u))
      =⟨ Lemma4.To.glue-β A B (A × B) C fst snd u |in-ctx snd×= ⟩
    snd×= (pair×= (glue (fst u)) idp)
      =⟨ snd×=-β (glue (fst u)) idp ⟩
    idp ∎

  lemma2'-2 : (u : (A × B) × C) → ap (lemma3'-fun C (A × C) snd ∘ M.f₃∙ (transpose join-assoc-span^2)) (glue u) == idp
  lemma2'-2 u =
    ap (lemma3'-fun C (A × C) snd ∘ M.f₃∙ (transpose join-assoc-span^2)) (glue u)
      =⟨ ap-∘ (lemma3'-fun C (A × C) snd) (M.f₃∙ (transpose join-assoc-span^2)) (glue u) ⟩
    ap (lemma3'-fun C (A × C) snd) (ap (M.f₃∙ (transpose join-assoc-span^2)) (glue u))
      =⟨ M.F₃∙.glue-β (transpose join-assoc-span^2) u |in-ctx ap (lemma3'-fun C (A × C) snd) ⟩
    ap (lemma3'-fun C (A × C) snd) (glue (fst (fst u) , snd u) ∙ idp)
      =⟨ ∙-unit-r (glue (fst (fst u) , snd u)) |in-ctx ap (lemma3'-fun C (A × C) snd) ⟩
    ap (lemma3'-fun C (A × C) snd) (glue (fst (fst u) , snd u))
      =⟨ Lemma3'Fun.glue-β C (A × C) snd (fst (fst u) , snd u) ⟩
    idp ∎

lemma1 : Pushout^2 join-assoc-span^2 == A * (B * C)
lemma1 = ap Pushout lemma2

lemma1' : Pushout^2 (transpose join-assoc-span^2) == (A * B) * C
lemma1' = ap Pushout lemma2'

*-assoc : A * (B * C) == (A * B) * C
*-assoc = ! lemma1 ∙ ua PP.theorem ∙ lemma1'
