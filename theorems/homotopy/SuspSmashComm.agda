{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.SuspSmash

module homotopy.SuspSmashComm where

module Σ∧Σ-PathElim
  {i} {j} {k} {A : Type i} {B : Type j} {C : Type k}
  (f g : ⊙Susp A ∧ ⊙Susp B → C)
  (n-n : f (smin north north) == g (smin north north))
  (n-s : f (smin north south) == g (smin north south))
  (s-n : f (smin south north) == g (smin south north))
  (s-s : f (smin south south) == g (smin south south))
  (n-m : ∀ b → Square n-n (ap (λ sb → f (smin north sb)) (merid b))
                          (ap (λ sb → g (smin north sb)) (merid b)) n-s)
  (s-m : ∀ b → Square s-n (ap (λ sb → f (smin south sb)) (merid b))
                          (ap (λ sb → g (smin south sb)) (merid b)) s-s)
  (m-n : ∀ a → Square n-n (ap (λ sa → f (smin sa north)) (merid a))
                          (ap (λ sa → g (smin sa north)) (merid a)) s-n)
  (m-s : ∀ a → Square n-s (ap (λ sa → f (smin sa south)) (merid a))
                          (ap (λ sa → g (smin sa south)) (merid a)) s-s)
  (m-m : ∀ a b →
    Cube (m-n a)
         (m-s a)
         (n-m b)
         (natural-square (λ sb → ap (λ sa → f (smin sa sb)) (merid a)) (merid b))
         (natural-square (λ sb → ap (λ sa → g (smin sa sb)) (merid a)) (merid b))
         (s-m b))
  (basel : f smbasel == g smbasel)
  (baser : f smbaser == g smbaser)
  (gluel-north : Square n-n (ap f (smgluel north)) (ap g (smgluel north)) basel)
  (gluel-south : Square s-n (ap f (smgluel south)) (ap g (smgluel south)) basel)
  (gluel-merid : ∀ a →
    Cube gluel-north
         gluel-south
         (m-n a)
         (natural-square (λ sa → ap f (smgluel sa)) (merid a))
         (natural-square (λ sa → ap g (smgluel sa)) (merid a))
         (natural-square (λ sa → basel) (merid a)))
  (gluer-north : Square n-n (ap f (smgluer north)) (ap g (smgluer north)) baser)
  (gluer-south : Square n-s (ap f (smgluer south)) (ap g (smgluer south)) baser)
  (gluer-merid : ∀ b →
    Cube gluer-north
         gluer-south
         (n-m b)
         (natural-square (λ a → ap f (smgluer a)) (merid b))
         (natural-square (λ a → ap g (smgluer a)) (merid b))
         (natural-square (λ a → baser) (merid b))
  )
  where

  private
    module M =
      SuspDoublePathElim
        (λ sa sb → f (smin sa sb))
        (λ sa sb → g (smin sa sb))
        n-n n-s s-n s-s n-m s-m m-n m-s m-m
    module P =
      SmashElim
        {P = λ sa∧sb → f sa∧sb == g sa∧sb}
        M.p
        basel
        baser
        (λ sa → ↓-='-from-square $
          Susp-elim
            {P = λ sa → Square (M.p sa north) (ap f (smgluel sa)) (ap g (smgluel sa)) basel}
            gluel-north
            gluel-south
            (λ a → cube-to-↓-square $
                   cube-shift-back (! (M.merid-north-square-β a)) $
                   gluel-merid a)
            sa)
        (λ sb → ↓-='-from-square $
          Susp-elim
            {P = λ sb → Square (M.p north sb) (ap f (smgluer sb)) (ap g (smgluer sb)) baser}
            gluer-north
            gluer-south
            (λ b → cube-to-↓-square $
                   cube-shift-back (! (M.north-merid-square-β b)) $
                   gluer-merid b)
            sb)

  open P using (f) public

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  private
    f : ⊙Susp (de⊙ X) ∧ ⊙Susp (de⊙ Y) → Susp (Susp (X ∧ Y))
    f = Susp-fmap (∧Σ-out X Y) ∘ Σ∧-out X (⊙Susp (de⊙ Y))

    g : ⊙Susp (de⊙ X) ∧ ⊙Susp (de⊙ Y) → Susp (Susp (X ∧ Y))
    g = Susp-flip ∘ Susp-fmap (Σ∧-out X Y) ∘ ∧Σ-out (⊙Susp (de⊙ X)) Y

    f-merid-x : ∀ x sy →
      ap (λ sx → f (smin sx sy)) (merid x)
      =-=
      merid (∧Σ-out-smin.f X Y x sy)
    f-merid-x x sy =
      ap (Susp-fmap (∧Σ-out X Y) ∘ Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) sy) (merid x)
        =⟪ ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) sy) (merid x) ⟫
      ap (Susp-fmap (∧Σ-out X Y)) (ap (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) sy) (merid x))
        =⟪ ap (ap (Susp-fmap (∧Σ-out X Y)))
              (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) sy x) ⟫
      ap (Susp-fmap (∧Σ-out X Y)) (merid (smin x sy))
        =⟪ SuspFmap.merid-β (∧Σ-out X Y) (smin x sy) ⟫
      merid (∧Σ-out-smin.f X Y x sy) ∎∎

    g-merid-y : ∀ sx y →
      ap (g ∘ smin sx) (merid y)
      =-=
      ! (merid (Σ∧-out-smin.f X Y y sx))
    g-merid-y sx y =
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y) ∘ ∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y sx) (merid y)
        =⟪ ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y sx) (merid y) ⟫
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (ap (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y sx) (merid y))
        =⟪ ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y sx y) ⟫
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin sx y))
        =⟪ ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin sx y)) ⟫
      ap Susp-flip (ap (Susp-fmap (Σ∧-out X Y)) (merid (smin sx y)))
        =⟪ ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin sx y)) ⟫
      ap Susp-flip (merid (Σ∧-out-smin.f X Y y sx))
        =⟪ SuspFlip.merid-β (Σ∧-out-smin.f X Y y sx) ⟫
      ! (merid (Σ∧-out-smin.f X Y y sx)) ∎∎

    n-n : f (smin north north) == g (smin north north)
    n-n = merid north

    n-s : f (smin north south) == g (smin north south)
    n-s = idp

    s-n : f (smin south north) == g (smin south north)
    s-n = idp

    s-s : f (smin south south) == g (smin south south)
    s-s = ! (merid south)

    n-m : ∀ y → Square n-n (ap (f ∘ smin north) (merid y))
                           (ap (g ∘ smin north) (merid y)) n-s
    n-m y = ap-cst north (merid y) ∙v⊡ (lb-square (merid north) ⊡v∙ ! (↯ (g-merid-y north y)))

    s-m : ∀ y → Square s-n (ap (f ∘ smin south) (merid y))
                           (ap (g ∘ smin south) (merid y)) s-s
    s-m y = ap-cst south (merid y) ∙v⊡ br-square (! (merid south)) ⊡v∙ ! (↯ (g-merid-y south y))

    m-n : ∀ x → Square n-n (ap (λ sx → f (smin sx north)) (merid x))
                           (ap (λ sx → g (smin sx north)) (merid x)) s-n
    m-n x = ↯ (f-merid-x x north) ∙v⊡ (lt-square (merid north) ⊡v∙ ! (ap-cst south (merid x)))

    m-s : ∀ x → Square n-s (ap (λ sx → f (smin sx south)) (merid x))
                           (ap (λ sx → g (smin sx south)) (merid x)) s-s
    m-s x = ↯ (f-merid-x x south) ∙v⊡ (tr-square (merid south) ⊡v∙ ! (ap-cst north (merid x)))

    m-m : ∀ x y →
      Cube (m-n x)
           (m-s x)
           (n-m y)
           (natural-square (λ sy → ap (λ sx → f (smin sx sy)) (merid x)) (merid y))
           (natural-square (λ sy → ap (λ sx → g (smin sx sy)) (merid x)) (merid y))
           (s-m y)
    m-m x y =
      custom-cube-∙v⊡
        (↯ (f-merid-x x north))
        (↯ (f-merid-x x south))
        (ap-cst north (merid y))
        (ap-cst south (merid y)) $
      cube-shift-top (! top-path) $
      custom-cube-⊡v∙
        (! (ap-cst south (merid x)))
        (ap-cst north (merid x))
        (! (↯ (g-merid-y north y)))
        (↯ (g-merid-y south y)) $
      cube-shift-bot (! bot-path) $
      custom-cube (merid north) (merid south) (ap merid (merid (smin x y)))
      where
      custom-cube-∙v⊡ : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ p₋₀₀' : a₀₀₀ == a₁₀₀} (q₋₀₀ : p₋₀₀ == p₋₀₀')
        {p₋₁₀ : a₀₁₀ == a₁₁₀}
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀' p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ p₋₀₁' : a₀₀₁ == a₁₀₁} (q₋₀₁ : p₋₀₁ == p₋₀₁')
        {p₋₁₁ : a₀₁₁ == a₁₁₁}
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁' p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ p₀₀₋' : a₀₀₀ == a₀₀₁} (q₀₀₋ : p₀₀₋ == p₀₀₋')
        {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ p₁₀₋' : a₁₀₀ == a₁₀₁} (q₁₀₋ : p₁₀₋ == p₁₀₋')
        {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋' p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋' p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ (! q₀₀₋ ∙v⊡ (! q₋₀₀ ∙h⊡ sq₋₀₋ ⊡h∙ q₋₀₁) ⊡v∙ q₁₀₋) sq₋₁₋ sq₁₋₋
        → Cube (q₋₀₀ ∙v⊡ sq₋₋₀) (q₋₀₁ ∙v⊡ sq₋₋₁) (q₀₀₋ ∙v⊡ sq₀₋₋) sq₋₀₋ sq₋₁₋ (q₁₀₋ ∙v⊡ sq₁₋₋)
      custom-cube-∙v⊡ idp idp idp idp c = c
      custom-cube-⊡v∙ : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ : a₀₀₀ == a₁₀₀}
        {p₋₁₀ p₋₁₀' : a₀₁₀ == a₁₁₀} (q₋₁₀ : p₋₁₀ == p₋₁₀')
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ : a₀₀₁ == a₁₀₁}
        {p₋₁₁ p₋₁₁' : a₀₁₁ == a₁₁₁} (q₋₁₁ : p₋₁₁' == p₋₁₁)
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ : a₀₀₀ == a₀₀₁}
        {p₀₁₋ p₀₁₋' : a₀₁₀ == a₀₁₁} (q₀₁₋ : p₀₁₋ == p₀₁₋')
        {p₁₀₋ : a₁₀₀ == a₁₀₁}
        {p₁₁₋ p₁₁₋' : a₁₁₀ == a₁₁₁} (q₁₁₋ : p₁₁₋' == p₁₁₋)
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀' p₀₁₋' p₁₁₋' p₋₁₁'} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ (square-symmetry (q₋₁₀ ∙v⊡ (q₀₁₋ ∙h⊡ square-symmetry sq₋₁₋ ⊡h∙ q₁₁₋) ⊡v∙ q₋₁₁)) sq₁₋₋
        → Cube (sq₋₋₀ ⊡v∙ q₋₁₀) (sq₋₋₁ ⊡v∙ ! q₋₁₁) (sq₀₋₋ ⊡v∙ q₀₁₋) sq₋₀₋ sq₋₁₋ (sq₁₋₋ ⊡v∙ ! q₁₁₋)
      custom-cube-⊡v∙ idp idp idp idp {sq₋₁₋ = sq₋₁₋} c =
        cube-shift-bot (square-sym-inv sq₋₁₋) c
      custom-cube : ∀ {i} {S : Type i} {n s : S}
        (p q : n == s) (r : p == q)
        → Cube (lt-square p)
               (tr-square q)
               (lb-square p)
               (horiz-degen-square r)
               (vert-degen-square (ap ! r))
               (br-square (! q))
      custom-cube p@idp q@.idp r@idp = idc
      top-path :
        ! (ap-cst north (merid y)) ∙v⊡
        (! (↯ (f-merid-x x north)) ∙h⊡
         natural-square (λ sy → ap (λ sx → f (smin sx sy)) (merid x)) (merid y) ⊡h∙
         ↯ (f-merid-x x south)) ⊡v∙
        ap-cst south (merid y)
        ==
        horiz-degen-square (ap merid (merid (smin x y)))
      top-path =
        ! (ap-cst north (merid y)) ∙v⊡
        (! (↯ (f-merid-x x north)) ∙h⊡
         natural-square (λ sy → ap (λ sx → f (smin sx sy)) (merid x)) (merid y) ⊡h∙
         ↯ (f-merid-x x south)) ⊡v∙
        ap-cst south (merid y)
          =⟨ ap (λ u → ! (ap-cst north (merid y)) ∙v⊡ u ⊡v∙ ap-cst south (merid y)) $
             natural-square-path
               (λ sy → merid (∧Σ-out-smin.f X Y x sy))
               (λ sy → ap (λ sx → f (smin sx sy)) (merid x))
               (λ sy → ↯ (f-merid-x x sy))
               (merid y) ⟩
        ! (ap-cst north (merid y)) ∙v⊡
        natural-square (λ sy → merid (∧Σ-out-smin.f X Y x sy)) (merid y) ⊡v∙
        ap-cst south (merid y)
          =⟨ natural-square-cst
               north
               south
               (λ sy → merid (∧Σ-out-smin.f X Y x sy))
               (merid y) ⟩
        horiz-degen-square (ap (merid ∘ ∧Σ-out-smin.f X Y x) (merid y))
          =⟨ ap horiz-degen-square (ap-∘ merid (∧Σ-out-smin.f X Y x) (merid y)) ⟩
        horiz-degen-square (ap merid (ap (∧Σ-out-smin.f X Y x) (merid y)))
          =⟨ ap (horiz-degen-square ∘ ap merid) (∧Σ-out-smin.merid-β X Y x y) ⟩
        horiz-degen-square (ap merid (merid (smin x y))) =∎
      bot-path :
        square-symmetry
         (! (ap-cst south (merid x)) ∙v⊡
          (! (↯ (g-merid-y north y)) ∙h⊡
           square-symmetry (natural-square
             (λ sy → ap (λ sx → g (smin sx sy)) (merid x)) (merid y)) ⊡h∙
           ↯ (g-merid-y south y)) ⊡v∙
          ap-cst north (merid x))
        ==
        vert-degen-square (ap ! (ap merid (merid (smin x y))))
      bot-path =
        square-symmetry
         (! (ap-cst south (merid x)) ∙v⊡
          (! (↯ (g-merid-y north y)) ∙h⊡
           square-symmetry (natural-square
             (λ sy → ap (λ sx → g (smin sx sy)) (merid x)) (merid y)) ⊡h∙
           ↯ (g-merid-y south y)) ⊡v∙
          ap-cst north (merid x))
          =⟨ ap (λ u → square-symmetry
                        (! (ap-cst south (merid x)) ∙v⊡
                         (! (↯ (g-merid-y north y)) ∙h⊡
                          u ⊡h∙
                          ↯ (g-merid-y south y)) ⊡v∙
                         ap-cst north (merid x))) $
             natural-square-symmetry
               (λ sx sy → g (smin sx sy))
               (merid x)
               (merid y) ⟩
        square-symmetry
         (! (ap-cst south (merid x)) ∙v⊡
          (! (↯ (g-merid-y north y)) ∙h⊡
           natural-square (λ sx → ap (g ∘ smin sx) (merid y)) (merid x) ⊡h∙
           ↯ (g-merid-y south y)) ⊡v∙
          ap-cst north (merid x))
          =⟨ ap (λ u → square-symmetry
                         (! (ap-cst south (merid x)) ∙v⊡ u ⊡v∙ ap-cst north (merid x))) $
             natural-square-path
               (λ sx → ! (merid (Σ∧-out-smin.f X Y y sx)))
               (λ sx → ap (g ∘ smin sx) (merid y))
               (λ sx → ↯ (g-merid-y sx y))
               (merid x) ⟩
        square-symmetry
         (! (ap-cst south (merid x)) ∙v⊡
          natural-square (λ sx → ! (merid (Σ∧-out-smin.f X Y y sx))) (merid x) ⊡v∙
          ap-cst north (merid x))
          =⟨ ap square-symmetry $
             natural-square-cst
               south
               north
               (λ sx → ! (merid (Σ∧-out-smin.f X Y y sx)))
               (merid x) ⟩
        square-symmetry
          (horiz-degen-square
            (ap (λ sx → ! (merid (Σ∧-out-smin.f X Y y sx))) (merid x)))
          =⟨ horiz-degen-square-symmetry
               (ap (λ sx → ! (merid (Σ∧-out-smin.f X Y y sx))) (merid x)) ⟩
        vert-degen-square (ap (! ∘ merid ∘ Σ∧-out-smin.f X Y y) (merid x))
          =⟨ ap vert-degen-square (ap-∘ (! ∘ merid) (Σ∧-out-smin.f X Y y) (merid x)) ⟩
        vert-degen-square (ap (! ∘ merid) (ap (Σ∧-out-smin.f X Y y) (merid x)))
          =⟨ ap (vert-degen-square ∘ ap (! ∘ merid)) (Σ∧-out-smin.merid-β X Y y x) ⟩
        vert-degen-square (ap (! ∘ merid) (merid (smin x y)))
          =⟨ ap vert-degen-square (ap-∘ ! merid (merid (smin x y))) ⟩
        vert-degen-square (ap ! (ap merid (merid (smin x y)))) =∎

    basel : f smbasel == g smbasel
    basel = merid north

    baser : f smbaser == g smbaser
    baser = merid north

    f-smgluel : ∀ sx → ap f (smgluel sx) == ap (Susp-fmap (∧Σ-out X Y)) (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y)) sx)
    f-smgluel sx =
      ap f (smgluel sx)
        =⟨ ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out X (⊙Susp (de⊙ Y))) (smgluel sx) ⟩
      ap (Susp-fmap (∧Σ-out X Y)) (ap (Σ∧-out X (⊙Susp (de⊙ Y))) (smgluel sx))
        =⟨ ap (ap (Susp-fmap (∧Σ-out  X Y)))
              (Σ∧Out.smgluel-β X (⊙Susp (de⊙ Y)) sx) ⟩
      ap (Susp-fmap (∧Σ-out X Y)) (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y)) sx) =∎

    f-smgluel-north : ap f (smgluel north) == idp
    f-smgluel-north = f-smgluel north

    f-smgluel-south : ap f (smgluel south) =-= ! (merid north)
    f-smgluel-south =
      ap f (smgluel south)
        =⟪ f-smgluel south ⟫
      ap (Susp-fmap (∧Σ-out X Y)) (! (merid (smin (pt X) north)))
        =⟪ ap-! (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north)) ⟫
      ! (ap (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north)))
        =⟪ ap ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ⟫
      ! (merid north) ∎∎

    g-smgluel : ∀ sx → ap g (smgluel sx) == idp
    g-smgluel sx =
      ap g (smgluel sx)
        =⟨ ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out (⊙Susp (de⊙ X)) Y) (smgluel sx) ⟩
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (ap (∧Σ-out (⊙Susp (de⊙ X)) Y) (smgluel sx))
        =⟨ ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧ΣOut.smgluel-β (⊙Susp (de⊙ X)) Y sx) ⟩
      idp =∎

    smgluel-north : Square n-n (ap f (smgluel north)) (ap g (smgluel north)) basel
    smgluel-north = f-smgluel-north ∙v⊡ hid-square ⊡v∙ ! (g-smgluel north)

    smgluel-south : Square s-n (ap f (smgluel south)) (ap g (smgluel south)) basel
    smgluel-south = ↯ f-smgluel-south ∙v⊡ rt-square (merid north) ⊡v∙ ! (g-smgluel south)

    custom-cube-⊡v∙ : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
      {p₀₋₀  : a₀₀₀ == a₀₁₀}
      {p₋₀₀ : a₀₀₀ == a₁₀₀}
      {p₋₁₀ p₋₁₀' : a₀₁₀ == a₁₁₀} (q₋₁₀ : p₋₁₀ == p₋₁₀')
      {p₁₋₀ : a₁₀₀ == a₁₁₀}
      {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left
      {p₀₋₁ : a₀₀₁ == a₀₁₁}
      {p₋₀₁ : a₀₀₁ == a₁₀₁}
      {p₋₁₁ p₋₁₁' : a₀₁₁ == a₁₁₁} (q₋₁₁ : p₋₁₁' == p₋₁₁)
      {p₁₋₁ : a₁₀₁ == a₁₁₁}
      {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
      {p₀₀₋ : a₀₀₀ == a₀₀₁}
      {p₀₁₋ p₀₁₋' : a₀₁₀ == a₀₁₁} (q₀₁₋ : p₀₁₋ == p₀₁₋')
      {p₁₀₋ : a₁₀₀ == a₁₀₁}
      {p₁₁₋ p₁₁₋' : a₁₁₀ == a₁₁₁} (q₁₁₋ : p₁₁₋ == p₁₁₋')
      {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
      {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
      {sq₋₁₋ : Square p₋₁₀' p₀₁₋' p₁₁₋ p₋₁₁'} -- bottom
      {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
      → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ (q₀₁₋ ∙v⊡ (q₋₁₀ ∙h⊡ sq₋₁₋ ⊡h∙ q₋₁₁) ⊡v∙ q₁₁₋) (sq₁₋₋ ⊡v∙ q₁₁₋)
      → Cube (sq₋₋₀ ⊡v∙ q₋₁₀) (sq₋₋₁ ⊡v∙ ! q₋₁₁) (sq₀₋₋ ⊡v∙ q₀₁₋) sq₋₀₋ sq₋₁₋ sq₁₋₋
    custom-cube-⊡v∙ idp idp idp idp c = c

    smgluel-merid : ∀ x →
      Cube smgluel-north
           smgluel-south
           (m-n x)
           (natural-square (λ sx → ap f (smgluel sx)) (merid x))
           (natural-square (λ sx → ap g (smgluel sx)) (merid x))
           (natural-square (λ sx → basel) (merid x))
    smgluel-merid x =
      custom-cube-∙v⊡
        f-smgluel-north
        (f-smgluel south) (↯ (tail f-smgluel-south))
        (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x))
        (↯ (tail (f-merid-x x north)))
        (ap-cst north (merid x)) $
      cube-shift-top (! (top-path x)) $
      custom-cube-⊡v∙
        (! (g-smgluel north))
        (g-smgluel south)
        (! (ap-cst south (merid x)))
        (ap-cst south (merid x)) $
      cube-shift-front (! (front-path x)) $
      cube-shift-bot (! (bot-path x)) $
      custom-cube (merid north)
      where
      custom-cube-∙v⊡ : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ p₋₀₀' : a₀₀₀ == a₁₀₀} (q₋₀₀ : p₋₀₀ == p₋₀₀')
        {p₋₁₀ : a₀₁₀ == a₁₁₀}
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀' p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ p₋₀₁' p₋₀₁'' : a₀₀₁ == a₁₀₁} (q₋₀₁ : p₋₀₁ == p₋₀₁') (q₋₀₁' : p₋₀₁' == p₋₀₁'')
        {p₋₁₁ : a₀₁₁ == a₁₁₁}
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁'' p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ p₀₀₋' p₀₀₋'' : a₀₀₀ == a₀₀₁} (q₀₀₋ : p₀₀₋ == p₀₀₋') (q₀₀₋' : p₀₀₋' == p₀₀₋'')
        {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ p₁₀₋' : a₁₀₀ == a₁₀₁} (q₁₀₋ : p₁₀₋ == p₁₀₋')
        {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋'' p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋
               ((! q₀₀₋' ∙v⊡ (! q₀₀₋ ∙v⊡ (! q₋₀₀ ∙h⊡ sq₋₀₋ ⊡h∙ q₋₀₁)) ⊡v∙ q₁₀₋) ⊡h∙ q₋₀₁')
               sq₋₁₋ (! q₁₀₋ ∙v⊡ sq₁₋₋)
        → Cube (q₋₀₀ ∙v⊡ sq₋₋₀) ((q₋₀₁ ∙ q₋₀₁') ∙v⊡ sq₋₋₁) ((q₀₀₋ ∙ q₀₀₋') ∙v⊡ sq₀₋₋) sq₋₀₋ sq₋₁₋ sq₁₋₋
      custom-cube-∙v⊡ idp idp idp idp idp idp c = c
      custom-cube : ∀ {i} {S : Type i} {n s : S} (p : n == s)
        → Cube hid-square (rt-square p) (lt-square p) (tr-square p) ids hid-square
      custom-cube p@idp = idc
      top-path : ∀ x →
        (! (↯ (tail (f-merid-x x north))) ∙v⊡
         (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
          (! f-smgluel-north ∙h⊡
           natural-square (λ sx → ap f (smgluel sx)) (merid x) ⊡h∙
           f-smgluel south)) ⊡v∙
         ap-cst north (merid x)) ⊡h∙
        ↯ (tail f-smgluel-south)
        ==
        tr-square (merid north)
      top-path x =
        (! (↯ (tail (f-merid-x x north))) ∙v⊡
         (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
          (! f-smgluel-north ∙h⊡
           natural-square (λ sx → ap f (smgluel sx)) (merid x) ⊡h∙
           f-smgluel south)) ⊡v∙
         ap-cst north (merid x)) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ap (λ u → (! (↯ (tail (f-merid-x x north))) ∙v⊡
                        (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
                         u) ⊡v∙
                        ap-cst north (merid x)) ⊡h∙
                       ↯ (tail f-smgluel-south)) $
             natural-square-path
               (ap (Susp-fmap (∧Σ-out X Y)) ∘ Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y)))
               (λ sx → ap f (smgluel sx))
               f-smgluel
               (merid x) ⟩
        (! (↯ (tail (f-merid-x x north))) ∙v⊡
         (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
          natural-square (ap (Susp-fmap (∧Σ-out X Y)) ∘ Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
         ap-cst north (merid x)) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ap (λ v → (! (↯ (tail (f-merid-x x north))) ∙v⊡
                        v ⊡v∙
                        ap-cst north (merid x)) ⊡h∙
                       ↯ (tail f-smgluel-south)) $
             ! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
             natural-square (ap (Susp-fmap (∧Σ-out X Y)) ∘ Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)
               =⟨ ap (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡_) $
                  natural-square-ap (Susp-fmap (∧Σ-out X Y)) (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x) ⟩
             ! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
             ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x) ∙v⊡
             ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
             ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)
               =⟨ ! $ ∙v⊡-assoc
                    (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)))
                    (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x))
                    (ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
                     ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) ⟩
             (! (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙
              ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ∙v⊡
             ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
             ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)
               =⟨ ap (_∙v⊡ ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
                           ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) $
                  !-inv-l (ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smin.f X (⊙Susp (de⊙ Y)) north) (merid x)) ⟩
             ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
             ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x) =∎ ⟩
        (! (↯ (tail (f-merid-x x north))) ∙v⊡
         (ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
          ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) ⊡v∙
         ap-cst north (merid x)) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ap (λ u → (! (↯ (tail (f-merid-x x north))) ∙v⊡
                        u) ⊡h∙
                       ↯ (tail f-smgluel-south)) $
             (ap-square (Susp-fmap (∧Σ-out X Y)) (natural-square (Σ∧OutSmgluel.f X (⊙Susp (de⊙ Y))) (merid x)) ⊡v∙
              ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) ⊡v∙
             ap-cst north (merid x)
               =⟨ ap (λ u → (ap-square (Susp-fmap (∧Σ-out X Y)) u ⊡v∙
                             ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) ⊡v∙
                            ap-cst north (merid x)) $
                  Σ∧OutSmgluel.merid-square-β X (⊙Susp (de⊙ Y)) x ⟩
             (ap-square (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x) ⊡v∙
              ∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x)) ⊡v∙
             ap-cst north (merid x)
               =⟨ ⊡v∙-assoc
                    (ap-square (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x))
                    (∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x))
                    (ap-cst north (merid x)) ⟩
             ap-square (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x) ⊡v∙
             (∘-ap (Susp-fmap (∧Σ-out X Y)) (λ _ → north) (merid x) ∙
              ap-cst north (merid x))
               =⟨ ap (ap-square (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x) ⊡v∙_) $
                  =ₛ-out $ ap-∘-cst-coh (Susp-fmap (∧Σ-out X Y)) north (merid x) ⟩
             ap-square (Susp-fmap (∧Σ-out X Y)) (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x) ⊡v∙
             ap (ap (Susp-fmap (∧Σ-out X Y))) (ap-cst north (merid x))
               =⟨ ap-square-⊡v∙
                    (Susp-fmap (∧Σ-out X Y))
                    (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x)
                    (ap-cst north (merid x)) ⟩
             ap-square
               (Susp-fmap (∧Σ-out X Y))
               (Σ∧-out-smgluel-merid X (⊙Susp (de⊙ Y)) x ⊡v∙ ap-cst north (merid x))
               =⟨ ap (ap-square (Susp-fmap (∧Σ-out X Y))) $
                  ⊡v∙-assoc
                    ((Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ∙v⊡
                     tr-square (merid (smin (pt X) north)))
                    (! (ap-cst north (merid x)))
                    (ap-cst north (merid x)) ⟩
             ap-square
               (Susp-fmap (∧Σ-out X Y))
               (((Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ∙v⊡
                 tr-square (merid (smin (pt X) north))) ⊡v∙
                (! (ap-cst north (merid x)) ∙ ap-cst north (merid x)))
               =⟨ ap (λ u → ap-square (Susp-fmap (∧Σ-out X Y)) $
                            ((Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙
                              ap merid (∧-norm-l x)) ∙v⊡
                             tr-square (merid (smin (pt X) north))) ⊡v∙
                            u) $
                  !-inv-l (ap-cst north (merid x)) ⟩
             ap-square
               (Susp-fmap (∧Σ-out X Y))
               ((Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ∙v⊡
                tr-square (merid (smin (pt X) north)))
               =⟨ ! $ ap-square-∙v⊡
                    (Susp-fmap (∧Σ-out X Y))
                    (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x))
                    (tr-square (merid (smin (pt X) north))) ⟩
             ap (ap (Susp-fmap (∧Σ-out X Y)))
                (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ∙v⊡
             ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north))) =∎
           ⟩
        (! (↯ (tail (f-merid-x x north))) ∙v⊡
         ap (ap (Susp-fmap (∧Σ-out X Y)))
            (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ∙v⊡
         ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north)))) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ! $ ap (_⊡h∙ ↯ (tail f-smgluel-south)) $
             ∙v⊡-assoc (! (↯ (tail (f-merid-x x north))))
                       (ap (ap (Susp-fmap (∧Σ-out X Y)))
                           (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)))
                       (ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north)))) ⟩
        ((! (↯ (tail (f-merid-x x north))) ∙
          ap (ap (Susp-fmap (∧Σ-out X Y)))
             (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x))) ∙v⊡
         ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north)))) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ap (λ u → (u ∙v⊡ ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north)))) ⊡h∙
                       ↯ (tail f-smgluel-south)) $ =ₛ-out $
             ! (↯ (tail (f-merid-x x north))) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y)))
                (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ◃∎
               =ₛ⟨ 0 & 1 & !-∙-seq (tail (f-merid-x x north)) ⟩
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin x north)) ◃∙
             ! (ap (ap (Susp-fmap (∧Σ-out X Y))) (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x)) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y)))
                (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ∙ ap merid (∧-norm-l x)) ◃∎
               =ₛ⟨ 2 & 1 &
                   ap-seq-∙
                     (ap (Susp-fmap (∧Σ-out X Y)))
                     (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x ◃∙
                      ap merid (∧-norm-l x) ◃∎) ⟩
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin x north)) ◃∙
             ! (ap (ap (Susp-fmap (∧Σ-out X Y))) (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x)) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y))) (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y))) (ap merid (∧-norm-l x)) ◃∎
               =ₛ⟨ 1 & 2 & seq-!-inv-l $
                   ap (ap (Susp-fmap (∧Σ-out X Y)))
                      (Σ∧-out-smin.merid-β X (⊙Susp (de⊙ Y)) north x) ◃∎ ⟩
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin x north)) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y))) (ap merid (∧-norm-l x)) ◃∎
               =ₛ₁⟨ 1 & 1 & ∘-ap (ap (Susp-fmap (∧Σ-out X Y))) merid (∧-norm-l x) ⟩
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin x north)) ◃∙
             ap (ap (Susp-fmap (∧Σ-out X Y)) ∘ merid) (∧-norm-l x) ◃∎
               =ₛ⟨ !ₛ $
                   homotopy-naturality
                     (merid ∘ ∧Σ-out X Y)
                     (ap (Susp-fmap (∧Σ-out X Y)) ∘ merid)
                     (! ∘ SuspFmap.merid-β (∧Σ-out X Y))
                     (∧-norm-l x) ⟩
             ap (merid ∘ ∧Σ-out X Y) (∧-norm-l x) ◃∙
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ◃∎
               =ₛ⟨ 0 & 1 & =ₛ-in {t = []} $
                   ap-∘ merid (∧Σ-out X Y) (∧-norm-l x) ∙
                   ap (ap merid) (∧Σ-out-∧-norm-l X Y x) ⟩
             ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ◃∎ ∎ₛ ⟩
        (! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡
         ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north)))) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ∙v⊡-⊡h∙-comm
               (! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)))
               (ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north))))
               (↯ (tail f-smgluel-south)) ⟩
        ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡
        ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north))) ⊡h∙
        ↯ (tail f-smgluel-south)
          =⟨ ! $ ap (! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡_) $
             ⊡h∙-assoc
               (ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north))))
               (ap-! (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north)))
               (ap ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north))) ⟩
        ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡
        ap-square (Susp-fmap (∧Σ-out X Y)) (tr-square (merid (smin (pt X) north))) ⊡h∙
        ap-! (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north)) ⊡h∙
        ap ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north))
          =⟨ ap (λ u → ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡
                       u ⊡h∙
                       ap ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north))) $
             ap-tr-square (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north)) ⟩
        ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ∙v⊡
        tr-square (ap (Susp-fmap (∧Σ-out X Y)) (merid (smin (pt X) north))) ⊡h∙
        ap ! (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north))
          =⟨ tr-square-∙v⊡-⊡h∙ (SuspFmap.merid-β (∧Σ-out X Y) (smin (pt X) north)) ⟩
        tr-square (merid north) =∎
      front-path : ∀ (x : de⊙ X) →
        (! (ap-cst north (merid x)) ∙v⊡
         natural-square (λ sx → basel) (merid x)) ⊡v∙
        ap-cst south (merid x)
        ==
        hid-square
      front-path x =
        (! (ap-cst north (merid x)) ∙v⊡
         natural-square (λ sx → basel) (merid x)) ⊡v∙
        ap-cst south (merid x)
          =⟨ ∙v⊡-⊡v∙-comm
               (! (ap-cst north (merid x)))
               (natural-square (λ sx → basel) (merid x))
               (ap-cst south (merid x)) ⟩
        ! (ap-cst north (merid x)) ∙v⊡
        natural-square (λ sx → basel) (merid x) ⊡v∙
        ap-cst south (merid x)
          =⟨ natural-square-cst north south (λ sx → basel) (merid x) ⟩
        horiz-degen-square (ap (λ sx → basel) (merid x))
          =⟨ ap horiz-degen-square (ap-cst basel (merid x)) ⟩
        horiz-degen-square idp
          =⟨ horiz-degen-square-idp ⟩
        hid-square =∎
      bot-path : ∀ (x : de⊙ X) →
        ! (ap-cst south (merid x)) ∙v⊡
        (! (g-smgluel north) ∙h⊡
         natural-square (λ sx → ap g (smgluel sx)) (merid x) ⊡h∙
         g-smgluel south) ⊡v∙
        ap-cst south (merid x)
        ==
        ids
      bot-path x =
        ! (ap-cst south (merid x)) ∙v⊡
        (! (g-smgluel north) ∙h⊡
         natural-square (λ sx → ap g (smgluel sx)) (merid x) ⊡h∙
         g-smgluel south) ⊡v∙
        ap-cst south (merid x)
          =⟨ ap (λ u → ! (ap-cst south (merid x)) ∙v⊡ u ⊡v∙ ap-cst south (merid x)) $
             natural-square-path
               (λ sx → idp)
               (λ sx → ap g (smgluel sx))
               g-smgluel
               (merid x) ⟩
        ! (ap-cst south (merid x)) ∙v⊡
        natural-square (λ sx → idp) (merid x) ⊡v∙
        ap-cst south (merid x)
          =⟨ natural-square-cst
               south
               south
               (λ sx → idp)
               (merid x) ⟩
        disc-to-square (ap (λ sx → idp) (merid x))
          =⟨ ap disc-to-square (ap-cst idp (merid x)) ⟩
        ids =∎

    f-smgluer : ∀ sy → ap f (smgluer sy) == idp
    f-smgluer sy =
      ap f (smgluer sy)
        =⟨ ap-∘ (Susp-fmap (∧Σ-out X Y)) (Σ∧-out X (⊙Susp (de⊙ Y))) (smgluer sy) ⟩
      ap (Susp-fmap (∧Σ-out X Y)) (ap (Σ∧-out X (⊙Susp (de⊙ Y))) (smgluer sy))
        =⟨ ap (ap (Susp-fmap (∧Σ-out  X Y)))
              (Σ∧Out.smgluer-β X (⊙Susp (de⊙ Y)) sy) ⟩
      idp =∎

    g-smgluer : ∀ sy →
      ap g (smgluer sy)
      ==
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y sy)
    g-smgluer sy =
      ap g (smgluer sy)
        =⟨ ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out (⊙Susp (de⊙ X)) Y) (smgluer sy) ⟩
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (ap (∧Σ-out (⊙Susp (de⊙ X)) Y) (smgluer sy))
        =⟨ ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧ΣOut.smgluer-β (⊙Susp (de⊙ X)) Y sy) ⟩
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y sy) =∎

    g-smgluer-north : ap g (smgluer north) == idp
    g-smgluer-north = g-smgluer north

    g-smgluer-south-step :
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))
      ==
      ! (merid north)
    g-smgluer-south-step = ↯ $
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))
        =⟪ ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))) ⟫
      ap Susp-flip (ap (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))))
        =⟪ ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north (pt Y))) ⟫
      ap Susp-flip (merid north)
        =⟪ SuspFlip.merid-β north ⟫
      ! (merid north) ∎∎

    g-smgluer-south : ap g (smgluer south) =-= merid north
    g-smgluer-south =
      ap g (smgluer south)
        =⟪ g-smgluer south ⟫
      ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (! (merid (smin north (pt Y))))
        =⟪ ap-! (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))) ⟫
      ! (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))))
        =⟪ ap ! g-smgluer-south-step ⟫
      ! (! (merid north))
        =⟪ !-! (merid north) ⟫
      merid north ∎∎

    smgluer-north : Square n-n (ap f (smgluer north)) (ap g (smgluer north)) baser
    smgluer-north = f-smgluer north ∙v⊡ hid-square ⊡v∙ ! g-smgluer-north

    smgluer-south : Square n-s (ap f (smgluer south)) (ap g (smgluer south)) baser
    smgluer-south = f-smgluer south ∙v⊡ br-square (merid north) ⊡v∙ ! (↯ (g-smgluer-south))

    smgluer-merid : ∀ (y : de⊙ Y) →
      Cube smgluer-north
           smgluer-south
           (n-m y)
           (natural-square (λ a → ap f (smgluer a)) (merid y))
           (natural-square (λ a → ap g (smgluer a)) (merid y))
           (natural-square (λ a → baser) (merid y))
    smgluer-merid y =
      smgluer-merid-custom-cube-∙v⊡
        (f-smgluer north)
        (f-smgluer south)
        (ap-cst north (merid y))
        (ap-cst north (merid y)) $
      cube-shift-top (! top-path) $
      custom-cube-⊡v∙
        (! g-smgluer-north)
        (↯ g-smgluer-south)
        (! (↯ (g-merid-y north y)))
        (ap-cst south (merid y)) $
      cube-shift-front (! front-path) $
      cube-shift-bot (! bot-path) $
      custom-cube (merid north)
      where
      smgluer-merid-custom-cube-∙v⊡ :
        ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ p₋₀₀' : a₀₀₀ == a₁₀₀} (q₋₀₀ : p₋₀₀' == p₋₀₀)
        {p₋₁₀ : a₀₁₀ == a₁₁₀}
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ p₋₀₁' : a₀₀₁ == a₁₀₁} (q₋₀₁ : p₋₀₁' == p₋₀₁)
        {p₋₁₁ : a₀₁₁ == a₁₁₁}
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ p₀₀₋' : a₀₀₀ == a₀₀₁} (q₀₀₋ : p₀₀₋' == p₀₀₋)
        {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ p₁₀₋' : a₁₀₀ == a₁₀₁} (q₁₀₋ : p₁₀₋ == p₁₀₋')
        {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀' p₀₀₋' p₁₀₋ p₋₀₁'} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ (! q₀₀₋ ∙v⊡ (! q₋₀₀ ∙h⊡ sq₋₀₋ ⊡h∙ q₋₀₁) ⊡v∙ q₁₀₋) sq₋₁₋ (! q₁₀₋ ∙v⊡ sq₁₋₋)
        → Cube (q₋₀₀ ∙v⊡ sq₋₋₀) (q₋₀₁ ∙v⊡ sq₋₋₁) (q₀₀₋ ∙v⊡ sq₀₋₋) sq₋₀₋ sq₋₁₋ sq₁₋₋
      smgluer-merid-custom-cube-∙v⊡ idp idp idp idp c = c
      top-path :
        ! (ap-cst north (merid y)) ∙v⊡
        (! (f-smgluer north) ∙h⊡
         natural-square (λ sy → ap f (smgluer sy)) (merid y) ⊡h∙
         f-smgluer south) ⊡v∙
        ap-cst north (merid y)
        ==
        ids
      top-path =
        ! (ap-cst north (merid y)) ∙v⊡
        (! (f-smgluer north) ∙h⊡
         natural-square (λ sy → ap f (smgluer sy)) (merid y) ⊡h∙
         f-smgluer south) ⊡v∙
        ap-cst north (merid y)
          =⟨ ap (λ u → ! (ap-cst north (merid y)) ∙v⊡ u ⊡v∙ ap-cst north (merid y)) $
             natural-square-path
               (λ sy → idp)
               (λ sy → ap f (smgluer sy))
               f-smgluer
               (merid y) ⟩
        ! (ap-cst north (merid y)) ∙v⊡
        natural-square (λ sy → idp) (merid y) ⊡v∙
        ap-cst north (merid y)
          =⟨ natural-square-cst
               north
               north
               (λ sy → idp)
               (merid y) ⟩
        disc-to-square (ap (λ sy → idp) (merid y))
          =⟨ ap disc-to-square (ap-cst idp (merid y)) ⟩
        ids =∎
      front-path :
        (! (ap-cst north (merid y)) ∙v⊡
         natural-square (λ sy → baser) (merid y)) ⊡v∙
        ap-cst south (merid y)
        ==
        hid-square
      front-path =
        (! (ap-cst north (merid y)) ∙v⊡
         natural-square (λ sy → baser) (merid y)) ⊡v∙
        ap-cst south (merid y)
          =⟨ ∙v⊡-⊡v∙-comm (! (ap-cst north (merid y)))
                          (natural-square (λ sy → baser) (merid y))
                          (ap-cst south (merid y)) ⟩
        ! (ap-cst north (merid y)) ∙v⊡
        natural-square (λ sy → baser) (merid y) ⊡v∙
        ap-cst south (merid y)
          =⟨ natural-square-cst
               north
               south
               (λ sy → baser)
               (merid y) ⟩
        horiz-degen-square (ap (λ sy → baser) (merid y))
          =⟨ ap horiz-degen-square (ap-cst baser (merid y)) ⟩
        horiz-degen-square idp
          =⟨ horiz-degen-square-idp ⟩
        hid-square =∎
      bot-path :
        ! (↯ (g-merid-y north y)) ∙v⊡
        (! g-smgluer-north ∙h⊡
         natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙
         ↯ g-smgluer-south) ⊡v∙
        ap-cst south (merid y)
        ==
        rt-square (merid north)
      bot-path =
        ! (↯ (g-merid-y north y)) ∙v⊡
        (! g-smgluer-north ∙h⊡
         natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙
         ↯ g-smgluer-south) ⊡v∙
        ap-cst south (merid y)
          =⟨ ap (λ u → ! (↯ (g-merid-y north y)) ∙v⊡ u ⊡v∙ ap-cst south (merid y)) $
             ! g-smgluer-north ∙h⊡
             natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙
             ↯ g-smgluer-south
               =⟨ ! $ ap (! g-smgluer-north ∙h⊡_) $
                  ⊡h∙-assoc
                    (natural-square (λ sy → ap g (smgluer sy)) (merid y))
                    (g-smgluer south)
                    (↯ (tail g-smgluer-south)) ⟩
             ! g-smgluer-north ∙h⊡
             natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙
             g-smgluer south ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ! $ ∙h⊡-⊡h∙-comm
                    (! g-smgluer-north)
                    (natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙ g-smgluer south)
                    (↯ (tail g-smgluer-south)) ⟩
             (! g-smgluer-north ∙h⊡
              natural-square (λ sy → ap g (smgluer sy)) (merid y) ⊡h∙
              g-smgluer south) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (_⊡h∙ ↯ (tail g-smgluer-south)) $
                  natural-square-path
                    (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) ∘ ∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y)
                    (λ sy → ap g (smgluer sy))
                    g-smgluer
                    (merid y) ⟩
             natural-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) ∘ ∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y) (merid y) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (_⊡h∙ ↯ (tail g-smgluer-south)) $
                  natural-square-ap
                    (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    (∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y)
                    (merid y) ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        (natural-square (∧ΣOutSmgluer.f (⊙Susp (de⊙ X)) Y) (merid y)) ⊡v∙
              ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (λ u → (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
                             ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) u ⊡v∙
                             ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⊡h∙
                            ↯ (tail g-smgluer-south)) $
                  ∧ΣOutSmgluer.merid-square-β (⊙Susp (de⊙ X)) Y y ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        (∧Σ-out-smgluer-merid (⊙Susp (de⊙ X)) Y y) ⊡v∙
              ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (λ u → (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
                             u ⊡v∙
                             ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⊡h∙
                            ↯ (tail g-smgluer-south)) $ ! $
                  ap-square-⊡v∙
                    (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                     tr-square (merid (smin north (pt Y))))
                    (! (ap-cst north (merid y))) ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                         tr-square (merid (smin north (pt Y)))) ⊡v∙
              ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (! (ap-cst north (merid y))) ⊡v∙
              ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (λ u → (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡ u) ⊡h∙
                            ↯ (tail g-smgluer-south)) $
                  ⊡v∙-assoc
                    (ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                       ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                        tr-square (merid (smin north (pt Y)))))
                    (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (! (ap-cst north (merid y))))
                    (∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y)) ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                         tr-square (merid (smin north (pt Y)))) ⊡v∙
              (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (! (ap-cst north (merid y))) ∙
               ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y))) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (λ u → (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
                             ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                                       ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                                        tr-square (merid (smin north (pt Y)))) ⊡v∙
                             u) ⊡h∙
                            ↯ (tail g-smgluer-south)) $ =ₛ-out $
                  ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (! (ap-cst north (merid y))) ◃∙
                  ∘-ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (λ _ → north) (merid y) ◃∎
                    =ₛ⟨ 1 & 1 &
                        post-rotate-in {p = _ ◃∎} $
                        ap-∘-cst-coh (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) north (merid y) ⟩
                  ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (! (ap-cst north (merid y))) ◃∙
                  ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (ap-cst north (merid y)) ◃∙
                  ! (ap-cst south (merid y)) ◃∎
                    =ₛ⟨ 0 & 2 & ap-seq-=ₛ (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) $
                                seq-!-inv-l (ap-cst north (merid y) ◃∎) ⟩
                  ! (ap-cst south (merid y)) ◃∎ ∎ₛ ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        ((∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                         tr-square (merid (smin north (pt Y)))) ⊡v∙
              ! (ap-cst south (merid y))) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ap (λ u → (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡ u ⊡v∙
                             (! (ap-cst south (merid y)))) ⊡h∙
                            ↯ (tail g-smgluer-south)) $ ! $
                  ap-square-∙v⊡
                    (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))
                    (tr-square (merid (smin north (pt Y)))) ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                  (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
               ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                         (tr-square (merid (smin north (pt Y))))) ⊡v∙
              ! (ap-cst south (merid y))) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ! $ ap (_⊡h∙ ↯ (tail g-smgluer-south)) $
                  ∙v⊡-⊡v∙-comm
                    (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y))
                    (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                        (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
                     ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                               (tr-square (merid (smin north (pt Y)))))
                    (! (ap-cst south (merid y))) ⟩
             (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙v⊡
              ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                 (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        (tr-square (merid (smin north (pt Y))))) ⊡v∙
             ! (ap-cst south (merid y)) ⊡h∙
             ↯ (tail g-smgluer-south)
               =⟨ ! $ ap (λ u → u ⊡v∙ ! (ap-cst south (merid y)) ⊡h∙ ↯ (tail g-smgluer-south)) $
                  ∙v⊡-assoc
                    (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y))
                    (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                        (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)))
                    (ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                               (tr-square (merid (smin north (pt Y))))) ⟩
             ((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
               ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                  (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
              ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                        (tr-square (merid (smin north (pt Y))))) ⊡v∙
             ! (ap-cst south (merid y)) ⊡h∙
             ↯ (tail g-smgluer-south) =∎
           ⟩
        ! (↯ (g-merid-y north y)) ∙v⊡
        (((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
           ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
          ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    (tr-square (merid (smin north (pt Y))))) ⊡v∙
         ! (ap-cst south (merid y)) ⊡h∙
         ↯ (tail g-smgluer-south)) ⊡v∙
        ap-cst south (merid y)
          =⟨ ap (! (↯ (g-merid-y north y)) ∙v⊡_) $ ! $
             ⊡v∙-⊡h∙-comm
               (((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
                  ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                     (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
                 ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                           (tr-square (merid (smin north (pt Y))))) ⊡v∙
                ! (ap-cst south (merid y)))
               (ap-cst south (merid y))
               (↯ (tail g-smgluer-south)) ⟩
        ! (↯ (g-merid-y north y)) ∙v⊡
        (((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
           ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
          ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    (tr-square (merid (smin north (pt Y))))) ⊡v∙
         ! (ap-cst south (merid y)) ⊡v∙
         ap-cst south (merid y)) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ap (λ u → ! (↯ (g-merid-y north y)) ∙v⊡ u ⊡h∙ ↯ (tail g-smgluer-south)) $
             ⊡v∙-assoc
               ((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
                 ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                    (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
                ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                          (tr-square (merid (smin north (pt Y)))))
               (! (ap-cst south (merid y)))
               (ap-cst south (merid y)) ⟩
        ! (↯ (g-merid-y north y)) ∙v⊡
        (((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
           ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
              (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
          ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                    (tr-square (merid (smin north (pt Y))))) ⊡v∙
         (! (ap-cst south (merid y)) ∙ ap-cst south (merid y))) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ap (λ u → ! (↯ (g-merid-y north y)) ∙v⊡
                       (((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
                          ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                             (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
                         ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                                   (tr-square (merid (smin north (pt Y))))) ⊡v∙
                        u) ⊡h∙
                       ↯ (tail g-smgluer-south)) $
             !-inv-l (ap-cst south (merid y)) ⟩
        ! (↯ (g-merid-y north y)) ∙v⊡
        ((ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
          ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
             (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
         ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                   (tr-square (merid (smin north (pt Y))))) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ap (! (↯ (g-merid-y north y)) ∙v⊡_) $
             ∙v⊡-⊡h∙-comm
               (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
                ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                   (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)))
               (ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                          (tr-square (merid (smin north (pt Y)))))
               (↯ (tail g-smgluer-south)) ⟩
        ! (↯ (g-merid-y north y)) ∙v⊡
        (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
         ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
            (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
        ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                  (tr-square (merid (smin north (pt Y)))) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ! $
             ∙v⊡-assoc
               (! (↯ (g-merid-y north y)))
               (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
                ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                   (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)))
               (ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                          (tr-square (merid (smin north (pt Y)))) ⊡h∙
                ↯ (tail g-smgluer-south)) ⟩
        (! (↯ (g-merid-y north y)) ∙
         ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ∙
         ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
            (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y))) ∙v⊡
        ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                  (tr-square (merid (smin north (pt Y)))) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ap (_∙v⊡ ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                                (tr-square (merid (smin north (pt Y)))) ⊡h∙
                      ↯ (tail g-smgluer-south)) $ =ₛ-out $
             ! (↯ (g-merid-y north y)) ◃∙
             ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ∙ ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 2 & 1 & ap-seq-∙ (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) $
                     (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y ◃∙
                      ap merid (∧-norm-r y) ◃∎) ⟩
             ! (↯ (g-merid-y north y)) ◃∙
             ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 0 & 1 & !-∙-seq (g-merid-y north y) ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north y))) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north y))) ◃∙
             ! (ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y)) ◃∙
             ! (ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y)) ◃∙
             ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 3 & 4 & seq-!-inv-l $
                   ap-∘ (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (∧Σ-out-smin.f (⊙Susp (de⊙ X)) Y north) (merid y) ◃∙
                   ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (∧Σ-out-smin.merid-β (⊙Susp (de⊙ X)) Y north y) ◃∎ ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north y))) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north y))) ◃∙
             ap (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))) (ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 2 & 2 & !ₛ $
                   homotopy-naturality
                     (ap Susp-flip ∘ ap (Susp-fmap (Σ∧-out X Y)))
                     (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)))
                     (λ p → ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) p))
                     (ap merid (∧-norm-r y)) ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north y))) ◃∙
             ap (ap Susp-flip ∘ ap (Susp-fmap (Σ∧-out X Y))) (ap merid (∧-norm-r y)) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ◃∎
               =ₛ₁⟨ 2 & 1 &
                    ∘-ap (ap Susp-flip ∘ ap (Susp-fmap (Σ∧-out X Y))) merid (∧-norm-r y) ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north y))) ◃∙
             ap (ap Susp-flip ∘ ap (Susp-fmap (Σ∧-out X Y)) ∘ merid) (∧-norm-r y) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ◃∎
               =ₛ⟨ 1 & 2 & !ₛ $
                   homotopy-naturality
                     (ap Susp-flip ∘ merid ∘ Σ∧Out.f X Y)
                     (ap Susp-flip ∘ ap (Susp-fmap (Σ∧-out X Y)) ∘ merid)
                     (λ w → ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) w)))
                     (∧-norm-r y) ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ap (ap Susp-flip ∘ merid ∘ Σ∧-out X Y) (∧-norm-r y) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north (pt Y)))) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ◃∎
               =ₛ⟨ 1 & 1 & =ₛ-in {t = []} $
                   ap-∘ (ap Susp-flip ∘ merid) (Σ∧-out X Y) (∧-norm-r y) ∙
                   ap (ap (ap Susp-flip ∘ merid)) (Σ∧-out-∧-norm-r X Y y) ⟩
             ! (SuspFlip.merid-β north) ◃∙
             ! (ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north (pt Y)))) ◃∙
             ! (ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ◃∎
               =ₛ⟨ ∙-!-seq $
                   ap-∘ Susp-flip (Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))) ◃∙
                   ap (ap Susp-flip) (SuspFmap.merid-β (Σ∧-out X Y) (smin north (pt Y))) ◃∙
                   SuspFlip.merid-β north ◃∎ ⟩
             ! g-smgluer-south-step ◃∎ ∎ₛ
           ⟩
        ! g-smgluer-south-step ∙v⊡
        ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                  (tr-square (merid (smin north (pt Y)))) ⊡h∙
        ↯ (tail g-smgluer-south)
          =⟨ ! $ ap (! g-smgluer-south-step ∙v⊡_) $
             ⊡h∙-assoc
               (ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                          (tr-square (merid (smin north (pt Y)))))
               (ap-! (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))))
               (ap ! g-smgluer-south-step ∙ !-! (merid north)) ⟩
        ! g-smgluer-south-step ∙v⊡
        ap-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y))
                  (tr-square (merid (smin north (pt Y)))) ⊡h∙
        ap-! (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))) ⊡h∙
        (ap ! g-smgluer-south-step ∙ !-! (merid north))
          =⟨ ap (λ u → ! g-smgluer-south-step ∙v⊡ u ⊡h∙
                       (ap ! g-smgluer-south-step ∙ !-! (merid north))) $
             ap-tr-square (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y))) ⟩
        ! g-smgluer-south-step ∙v⊡
        tr-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ⊡h∙
        (ap ! g-smgluer-south-step ∙ !-! (merid north))
          =⟨ ! $ ap (! g-smgluer-south-step ∙v⊡_) $
             ⊡h∙-assoc
               (tr-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))))
               (ap ! g-smgluer-south-step)
               (!-! (merid north)) ⟩
        ! g-smgluer-south-step ∙v⊡
        tr-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ⊡h∙
        ap ! g-smgluer-south-step ⊡h∙
        !-! (merid north)
          =⟨ ! $ ∙v⊡-⊡h∙-comm
               (! g-smgluer-south-step)
               (tr-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ⊡h∙
                ap ! g-smgluer-south-step)
               (!-! (merid north)) ⟩
        (! g-smgluer-south-step ∙v⊡
         tr-square (ap (Susp-flip ∘ Susp-fmap (Σ∧-out X Y)) (merid (smin north (pt Y)))) ⊡h∙
         ap ! g-smgluer-south-step) ⊡h∙
        !-! (merid north)
          =⟨ ap (_⊡h∙ !-! (merid north)) $
             tr-square-∙v⊡-⊡h∙ g-smgluer-south-step ⟩
        tr-square (! (merid north)) ⊡h∙ !-! (merid north)
          =⟨ tr-square-! (merid north) ⟩
        rt-square (merid north) =∎
      custom-cube : ∀ {i} {S : Type i} {n s : S} (p : n == s)
        → Cube hid-square (br-square p) (lb-square p) ids (rt-square p) hid-square
      custom-cube p@idp = idc

  module ∧Σ-Σ∧-Out =
    Σ∧Σ-PathElim
      f g
      n-n n-s s-n s-s
      n-m s-m m-n m-s
      m-m
      basel
      baser
      smgluel-north
      smgluel-south
      smgluel-merid
      smgluer-north
      smgluer-south
      smgluer-merid

  ∧Σ-Σ∧-out : Susp-fmap (∧Σ-out X Y) ∘ Σ∧-out X (⊙Susp (de⊙ Y))
            ∼ Susp-flip ∘ Susp-fmap (Σ∧-out X Y) ∘ ∧Σ-out (⊙Susp (de⊙ X)) Y
  ∧Σ-Σ∧-out = ∧Σ-Σ∧-Out.f
