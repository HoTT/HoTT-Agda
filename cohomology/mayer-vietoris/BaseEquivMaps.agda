{-# OPTIONS --without-K #-}

open import HoTT

{- Definition of the maps
     into : Cofiber reglue → ΣZ
     out  : ΣZ → Cofiber reglue
 -}

module cohomology.mayer-vietoris.BaseEquivMaps {i j k} {A : Type i}
  {B : Type j} (Z : Ptd k) (f : fst Z → A) (g : fst Z → B) where

X = ∙[ A , f (snd Z) ]
Y = ∙[ B , g (snd Z) ]
ps = ptd-span X Y Z (f , idp) (g , idp)
F : fst (Z ∙→ X)
F = (f , idp)
G : fst (Z ∙→ Y)
G = (g , idp)

open import cohomology.mayer-vietoris.Functions ps

module IntoCod = PushoutRec {d = ptd-span-out ps} {D = Suspension (fst Z)}
  (λ x → north _)
  (λ y → south _)
  (merid _)

into-cod = IntoCod.f

into-glue-square :
  Square idp idp (ap (into-cod ∘ reglue) wglue) (merid _ (snd Z))
into-glue-square =
  connection2
  ⊡v∙ ! (ap-∘ into-cod reglue wglue ∙ ap (ap into-cod) (Reglue.glue-β tt)
         ∙ IntoCod.glue-β (snd Z))

module IntoGlue = WedgeElim {P = λ xy → north _ == into-cod (reglue xy)}
  (λ _ → idp)
  (λ _ → merid _ (snd Z))
  (↓-cst=app-from-square into-glue-square)

into-glue = IntoGlue.f

module Into = CofiberRec reglue (north _) into-cod into-glue


out-glue-and-square : (z : fst Z)
  → Σ (cfbase reglue == cfbase reglue)
      (λ p → Square (cfglue _ (winl (f z))) p
               (ap (cfcod _) (glue z)) (cfglue _ (winr (g z))))
out-glue-and-square z = fill-square-top _ _ _

out-glue = fst ∘ out-glue-and-square
out-square = snd ∘ out-glue-and-square

module Out = SuspensionRec (fst Z) {C = Cofiber reglue}
  (cfbase _)
  (cfbase _)
  out-glue


into = Into.f
out = Out.f
