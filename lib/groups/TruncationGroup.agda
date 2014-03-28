{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Pi
open import lib.types.Truncation

module lib.groups.TruncationGroup where

module _ {i} {El : Type i} (GS : GroupStructure El) where

  Trunc-group-struct : GroupStructure (Trunc ⟨0⟩ El)
  Trunc-group-struct = record {
    ident = [ ident GS ];
    inv = Trunc-fmap (inv GS);
    comp = Trunc-fmap2 (comp GS);
    unitl = 
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ unitl GS);
    unitr = 
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ unitr GS);
    assoc = Trunc-elim
      (λ _ → Π-level (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level)))
      (λ a → Trunc-elim
        (λ _ → Π-level (λ _ → =-preserves-level _ Trunc-level))
        (λ b → Trunc-elim 
           (λ _ → =-preserves-level _ Trunc-level) 
           (λ c → ap [_] (assoc GS a b c))));
    invl = 
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ invl GS);
    invr = 
      Trunc-elim (λ _ → =-preserves-level _ Trunc-level) (ap [_] ∘ invr GS) }
    where open GroupStructure

  Trunc-Group : Group i
  Trunc-Group = record { 
    El = Trunc ⟨0⟩ El; 
    El-level = Trunc-level;
    group-struct = Trunc-group-struct }
