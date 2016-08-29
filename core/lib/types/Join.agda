{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout

module lib.types.Join  where

module _ {i j} (A : Type i) (B : Type j) where

  *-span : Span
  *-span = span A B (A × B) fst snd

  infix 80 _*_

  _*_ : Type _
  _*_ = Pushout *-span

module JoinElim {i j} {A : Type i} {B : Type j} {k} {P : A * B → Type k}
  (left* : (a : A) → P (left a)) (right* : (b : B) → P (right b))
  (glue* : (ab : A × B) → left* (fst ab) == right* (snd ab) [ P ↓ glue ab ])
  = PushoutElim left* right* glue*
open JoinElim public using () renaming (f to Join-elim)

module JoinRec {i j} {A : Type i} {B : Type j} {k} {D : Type k}
  (left* : (a : A) → D) (right* : (b : B) → D)
  (glue* : (ab : A × B) → left* (fst ab) == right* (snd ab))
  = PushoutRec left* right* glue*
open JoinRec public using () renaming (f to Join-rec)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  *-⊙span : ⊙Span
  *-⊙span = ⊙span X Y (X ⊙× Y) ⊙fst ⊙snd

  infix 80 _⊙*_

  _⊙*_ : Ptd _
  _⊙*_ = ⊙Pushout *-⊙span

module _ {i i' j j'} {A : Type i} {A' : Type i'} {B : Type j} {B' : Type j'} where

  *-emap : A ≃ A' → B ≃ B' → A * B ≃ A' * B'
  *-emap eqA eqB = equiv to from to-from from-to where
    module To = JoinRec {D = A' * B'} (left ∘ –> eqA) (right ∘ –> eqB) (λ{(a , b) → glue (–> eqA a , –> eqB b)})
    module From = JoinRec {D = A * B} (left ∘ <– eqA) (right ∘ <– eqB) (λ{(a , b) → glue (<– eqA a , <– eqB b)})

    to : A * B → A' * B'
    to = To.f

    from : A' * B' → A * B
    from = From.f

    abstract
      to-from : ∀ y → to (from y) == y
      to-from = Join-elim (ap left ∘ <–-inv-r eqA) (ap right ∘ <–-inv-r eqB) to-from-glue where
        to-from-glue : ∀ (ab : A' × B')
          → ap left (<–-inv-r eqA (fst ab)) == ap right (<–-inv-r eqB (snd ab)) [ (λ y → to (from y) == y) ↓ glue ab ]
        to-from-glue (a , b) = ↓-app=idf-in $
          ap left (<–-inv-r eqA a) ∙' glue (a , b)
            =⟨ htpy-natural'-app=cst (λ a → glue (a , b)) (<–-inv-r eqA a) ⟩
          glue (–> eqA (<– eqA a) , b)
            =⟨ ! $ htpy-natural-cst=app (λ b → glue (–> eqA (<– eqA a) , b)) (<–-inv-r eqB b) ⟩
          glue (–> eqA (<– eqA a) , –> eqB (<– eqB b)) ∙ ap right (<–-inv-r eqB b)
            =⟨ ! $ To.glue-β (<– eqA a , <– eqB b) |in-ctx (_∙ ap right (<–-inv-r eqB b)) ⟩
          ap to (glue (<– eqA a , <– eqB b)) ∙ ap right (<–-inv-r eqB b)
            =⟨ ! $ From.glue-β (a , b) |in-ctx (λ p → ap to p ∙ ap right (<–-inv-r eqB b)) ⟩
          ap to (ap from (glue (a , b))) ∙ ap right (<–-inv-r eqB b)
            =⟨ ! $ ap-∘ to from (glue (a , b)) |in-ctx (_∙ ap right (<–-inv-r eqB b)) ⟩
          ap (to ∘ from) (glue (a , b)) ∙ ap right (<–-inv-r eqB b)
            =∎

      from-to : ∀ x → from (to x) == x
      from-to = Join-elim (ap left ∘ <–-inv-l eqA) (ap right ∘ <–-inv-l eqB) from-to-glue where
        from-to-glue : ∀ (ab : A × B)
          → ap left (<–-inv-l eqA (fst ab)) == ap right (<–-inv-l eqB (snd ab)) [ (λ x → from (to x) == x) ↓ glue ab ]
        from-to-glue (a , b) = ↓-app=idf-in $
          ap left (<–-inv-l eqA a) ∙' glue (a , b)
            =⟨ htpy-natural'-app=cst (λ a → glue (a , b)) (<–-inv-l eqA a) ⟩
          glue (<– eqA (–> eqA a) , b)
            =⟨ ! $ htpy-natural-cst=app (λ b → glue (<– eqA (–> eqA a) , b)) (<–-inv-l eqB b) ⟩
          glue (<– eqA (–> eqA a) , <– eqB (–> eqB b)) ∙ ap right (<–-inv-l eqB b)
            =⟨ ! $ From.glue-β (–> eqA a , –> eqB b) |in-ctx (_∙ ap right (<–-inv-l eqB b)) ⟩
          ap from (glue (–> eqA a , –> eqB b)) ∙ ap right (<–-inv-l eqB b)
            =⟨ ! $ To.glue-β (a , b) |in-ctx (λ p → ap from p ∙ ap right (<–-inv-l eqB b)) ⟩
          ap from (ap to (glue (a , b))) ∙ ap right (<–-inv-l eqB b)
            =⟨ ! $ ap-∘ from to (glue (a , b)) |in-ctx (_∙ ap right (<–-inv-l eqB b)) ⟩
          ap (from ∘ to) (glue (a , b)) ∙ ap right (<–-inv-l eqB b)
            =∎

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'} where

  ⊙*-emap : X ⊙≃ X' → Y ⊙≃ Y' → X ⊙* Y ⊙≃ X' ⊙* Y'
  ⊙*-emap ⊙eqX ⊙eqY = ≃-to-⊙≃ (*-emap (⊙≃-to-≃ ⊙eqX) (⊙≃-to-≃ ⊙eqY)) (ap left (snd (⊙–> ⊙eqX)))
