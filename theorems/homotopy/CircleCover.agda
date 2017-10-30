{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.CircleCover {j} where

record S¹Cover : Type (lsucc j) where
  constructor s¹cover
  field
    El : Type j
    {{El-level}} : is-set El
    El-auto : El ≃ El

S¹cover-to-S¹-cover : S¹Cover → Cover S¹ j
S¹cover-to-S¹-cover sc = record {
  Fiber = S¹-rec El (ua El-auto);
  Fiber-level = λ {a} → S¹-elim {P = λ a → is-set (S¹-rec El (ua El-auto) a)} El-level prop-has-all-paths-↓ a}
  where open S¹Cover sc

S¹-cover-to-S¹cover : Cover S¹ j → S¹Cover
S¹-cover-to-S¹cover c = record {
  El = Fiber base;
  El-auto = coe-equiv (ap Fiber loop)}
  where open Cover c

S¹cover-equiv-S¹-cover : S¹Cover ≃ Cover S¹ j
S¹cover-equiv-S¹-cover = equiv to from to-from from-to where
  to = S¹cover-to-S¹-cover
  from = S¹-cover-to-S¹cover 
  to-from : ∀ c → to (from c) == c
  to-from c = cover=' $ λ= $
    S¹-elim idp $ ↓-='-in' $ ! $
      ap (S¹-rec (Fiber base) (ua (coe-equiv (ap Fiber loop)))) loop
        =⟨ S¹Rec.loop-β _ _ ⟩
      ua (coe-equiv (ap Fiber loop))
        =⟨ ua-η _ ⟩
      ap Fiber loop
        =∎
    where open Cover c
  from-to : ∀ sc → from (to sc) == sc
  from-to sc = ap (λ eq → s¹cover El eq) $
    coe-equiv (ap (S¹-rec El (ua El-auto)) loop)
      =⟨ ap coe-equiv $ S¹Rec.loop-β _ _ ⟩
    coe-equiv (ua El-auto)
      =⟨ coe-equiv-β El-auto ⟩
    El-auto
      =∎
    where open S¹Cover sc
