{-# OPTIONS --safe #-}

-- https://dl.acm.org/doi/10.1145/3573105.3575690

module MyhillCB.MyhillIso where

open import MyhillCB.Imports
open import MyhillCB.Base
open import MyhillCB.Least
open import MyhillCB.Properties
open import MyhillCB.Remove
open import Cubical.Data.Empty as ⊥


module Find {X Y : Type} (XYdisc : Discrete (X × Y))
            {P : X → Type} {Q : Y → Type} (redPQ : P ≼₁ Q) where

    private
        _∈₁_ : X → List (X × Y) → Type
        x ∈₁ C = x ∈₁⟨ XYdisc ⟩ C
        _∈₂_ : Y → List (X × Y) → Type
        y ∈₂ C = y ∈₂⟨ XYdisc ⟩ C

    open _≼₁_
    f : X → Y
    f = redPQ .fun
    P⇔Qf : ∀ x → P x ⇔ Q (f x)
    P⇔Qf = redPQ .Px⇔Qfx
    P→Qf : ∀ {x} → P x → Q (f x)
    P→Qf {x} = P⇔Qf x .fst
    Qf→P : ∀ {x} → Q (f x) → P x
    Qf→P {x} = P⇔Qf x .snd
    fInj : isInjective f
    fInj = redPQ .funInj

    γ-work-aux : (n : ℕ) → (∀ m → m < n → (xys : List (X × Y)) → length xys ≡ m → X → X) →
                 (xys : List (X × Y)) → length xys ≡ n →
                 (x : X) → Dec (f x ∈₂ xys) → X
    γ-work-aux n IH xys p x (no  _) = x
    γ-work-aux n IH xys p x (yes (x' , x'fxin)) = IH (length (new-xys)) ineq new-xys refl x' where
        new-xys : List (X × Y)
        new-xys = remove (_≡ (x' , f x)) (λ _ → XYdisc _ _) xys
        ineq : length new-xys < n
        ineq = subst (length new-xys <_) p
               (remove< (_≡ (x' , f x)) (λ _ → XYdisc _ _) xys XYdisc x'fxin refl)

    γ-work : (n : ℕ) → (∀ m → m < n → (xys : List (X × Y)) → length xys ≡ m → X → X) →
             (xys : List (X × Y)) → length xys ≡ n → X → X
    γ-work n IH xys p x = γ-work-aux n IH xys p x ((f x) ∈?₂⟨ XYdisc ⟩ xys)

    γ-len : (n : ℕ) → (xys : List (X × Y)) → length xys ≡ n → X → X
    γ-len = WFI.induction <-wellfounded γ-work

    γ : List (X × Y) → X → X
    γ C = γ-len (length C) C refl

    γlen-compute : (C : List (X × Y)) →
                γ-len (length C) ≡ γ-work (length C) (λ n _ → γ-len n)
    γlen-compute C = WFI.induction-compute <-wellfounded γ-work (length C)

    γ-compute : (C : List (X × Y)) → (x : X) →
                γ C x ≡ γ-work (length C) (λ n _ → γ-len n) C refl x
    γ-compute C x i = γlen-compute C i C refl x


    γ-specs : ℕ → Type
    γ-specs n = (C : List (X × Y)) → (p : length C ≡ n) →
                isCorrSeq C P Q XYdisc → (x : X) → ¬ (x ∈₁ C) →
                (fxin? : Dec (f x ∈₂ C)) → (f x) ∈?₂⟨ XYdisc ⟩ C ≡ fxin? →
                     ((P x ⇔ P (γ C x))
                    × ((γ C x ≡ x) ⊎ (γ C x ∈₁ C))
                    × (¬ (f (γ C x) ∈₂ C)))

    open isCorrSeq

    γspec-work : (n : ℕ) → (∀ m → m < n → γ-specs m) → γ-specs n

    γspec-work n IH C len=n Cseq x ¬xin (no ¬fxin2) p =
        ((subst P (sym γCx=x) , subst P γCx=x) , inl γCx=x , ¬fγin2) where
            γCx=x : γ C x ≡ x
            γCx=x = γ-compute C x ∙ cong (γ-work-aux (length C) (λ a _ → γ-len a) C refl x) p
            ¬fγin2 : ¬ (f (γ C x) ∈₂ C)
            ¬fγin2 (x1 , x1fγin) = ¬fxin2 (x1 , subst (λ y1 → (x1 , y1) ∈⟨ XYdisc ⟩ C) (cong f γCx=x) x1fγin)

    γspec-work n IH C len=n Cseq x ¬xin (yes (x' , x'fxin)) p = ((s1 , s2) , inr s3 , s4) where
        C' : List (X × Y)
        C' = remove (_≡ (x' , f x)) (λ _ → XYdisc _ _) C
        inC'→inC : {xy : (X × Y)} → xy ∈⟨ XYdisc ⟩ C' → xy ∈⟨ XYdisc ⟩ C
        inC'→inC = remove∈ (_≡ (x' , f x)) (λ _ → XYdisc _ _) C XYdisc

        ineq : length C' < n
        ineq = subst (length C' <_) len=n
            (remove< (_≡ (x' , f x)) (λ _ → XYdisc _ _) C XYdisc x'fxin refl)
        C'seq : isCorrSeq C' P Q XYdisc
        C'seq = removeCorrSeq (_≡ (x' , f x)) (λ _ → XYdisc _ _) Cseq
        ¬x'in : ¬ (x' ∈₁ C')
        ¬x'in (y  , x'yin') = ∉remove (_≡ (x' , f x)) (λ _ → XYdisc _ _) C XYdisc
            (ΣPathP (refl , Cseq .c2 (x' , y) (inC'→inC x'yin') (f x) x'fxin)) x'yin'

        inducted = IH (length C') ineq C' refl C'seq x' ¬x'in (f x' ∈?₂⟨ XYdisc ⟩ C') refl

        γ=γ' : γ C x ≡ γ C' x'
        γ=γ' = γ-compute C x ∙ cong (γ-work-aux (length C) (λ a _ → γ-len a) C refl x) p

        s1 : P x → P (γ C x)
        s1 Px = subst P (sym γ=γ') (inducted .fst .fst Px') where
            Px' : P x'
            Px' = Cseq .c1 (x' , f x) x'fxin .snd (P→Qf Px)

        s2 : P (γ C x) → P x
        s2 PγCx = Qf→P (Cseq .c1 (x' , f x) x'fxin .fst Px') where
            Px' : P x'
            Px' = inducted .fst .snd (subst P γ=γ' PγCx)

        s3 : γ C x ∈₁ C
        s3 with inducted .snd .fst
        ... | inl γ'=x' = f x , subst (λ a → (a , f x) ∈⟨ XYdisc ⟩ C) (sym (γ=γ' ∙ γ'=x')) x'fxin
        ... | inr (y , γ'yin') = y , inC'→inC (subst (λ a → (a , y) ∈⟨ XYdisc ⟩ C') (sym γ=γ') γ'yin')

        s4 : ¬ (f (γ C x) ∈₂ C)
        s4 (x1 , x1fγin) = inducted .snd .snd (x1 , subst (λ a → (x1 , f a) ∈⟨ XYdisc ⟩ C') γ=γ' answer) where
            answer : (x1 , f (γ C x)) ∈⟨ XYdisc ⟩ C'
            answer with XYdisc (x1 , f (γ C x)) (x' , f x)
            ... | no ¬p2 = ∈remove (_≡ (x' , f x)) (λ _ → XYdisc _ _) C XYdisc ¬p2 x1fγin
            ... | yes p2 = ⊥.rec (¬xin (subst (λ a → a ∈₁ C) (fInj (PathPΣ p2 .snd)) s3))


    γ-properties : ∀ n → γ-specs n
    γ-properties = WFI.induction <-wellfounded γspec-work

    find : List (X × Y) → X → Y
    find C x = f (γ C x)

    spec' : ∀ {C} {x} → isCorrSeq C P Q XYdisc → ¬ (x ∈₁ C) →
             (¬ (find C x ∈₂ C)) × (P x ⇔ Q (find C x))
    spec' {C} {x} Cseq ¬xin =
        γ-pfs .snd .snd , (γ-pfs .fst) ⊚ (P⇔Qf (γ C x)) where
            γ-pfs = γ-properties (length C) C refl Cseq x ¬xin (f x ∈?₂⟨ XYdisc ⟩ C) refl

    spec : ∀ {C} {x} → isCorrSeq C P Q XYdisc → ¬ (x ∈₁ C)
            → isCorrSeq ((x , find C x) ∷ C) P Q XYdisc
    spec {C} {x} Cseq ¬xin .c1 = allCons C XYdisc (spec' Cseq ¬xin .snd) (Cseq .c1)
    spec {C} {x} Cseq ¬xin .c2 = allCons C XYdisc Pf PC where
        Pf : (y' : Y) → (x , y') ∈⟨ XYdisc ⟩ ((x , find C x) ∷ C) → find C x ≡ y'
        Pf y' xy'in' with XYdisc (x , find C x) (x , y')
        ... | yes p = snd (PathPΣ p)
        ... | no _ = ⊥.rec (¬xin (y' , xy'in'))

        PC : ((x' , y') : X × Y) → (x' , y') ∈⟨ XYdisc ⟩ C →
             ∀ y → (x' , y) ∈⟨ XYdisc ⟩ ((x , find C x) ∷ C) → y' ≡ y
        PC (x' , y') x'y'in y x'yin' with XYdisc (x , find C x) (x' , y)
        ... | yes p = ⊥.rec (¬xin (y' , subst (λ a → (a , y') ∈⟨ XYdisc ⟩ C) (sym (fst (PathPΣ p))) x'y'in))
        ... | no _ = Cseq .c2 (x' , y') x'y'in y x'yin'

    spec {C} {x} Cseq ¬xin .c3 = allCons C XYdisc Pf PC where
        Pf : (x' : X) → (x' , find C x) ∈⟨ XYdisc ⟩ ((x , find C x) ∷ C) → x ≡ x'
        Pf x' x'fin' with XYdisc (x , find C x) (x' , find C x)
        ... | yes p = fst (PathPΣ p)
        ... | no _ = ⊥.rec (spec' Cseq ¬xin .fst (x' , x'fin'))

        PC : ((x1 , y1) : X × Y) → (x1 , y1) ∈⟨ XYdisc ⟩ C →
             ∀ x' → (x' , y1) ∈⟨ XYdisc ⟩ ((x , find C x) ∷ C) → x1 ≡ x'
        PC (x1 , y1) x1y1in x' x'y1in' with XYdisc (x , find C x) (x' , y1)
        ... | yes p = ⊥.rec (spec' Cseq ¬xin .fst (x1 , subst (λ a → (x1 , a) ∈⟨ XYdisc ⟩ C) (sym (snd (PathPΣ p))) x1y1in))
        ... | no _ = Cseq .c3 (x1 , y1) x1y1in x' x'y1in'



module Myhill {X Y : Type}
        (Xenum@(enumerateX , surjX) : Enumerable X) (Yenum@(enumerateY , surjY) : Enumerable Y)
        (Xdisc : Discrete X) (Ydisc : Discrete Y) where

  XYdisc : Discrete (X × Y)
  XYdisc = discProd Xdisc Ydisc
  YXdisc : Discrete (Y × X)
  YXdisc = discSwap XYdisc

  Xretℕ : X isRetractOf ℕ
  Xretℕ = EnumDisc→Retractℕ Xenum Xdisc
  IX : X → ℕ
  IX = Xretℕ .fst
  RX : ℕ → Opt X
  RX = Xretℕ .snd .fst
  retX : ∀ x → RX (IX x) ≡ Some x
  retX = Xretℕ .snd .snd

  Yretℕ : Y isRetractOf ℕ
  Yretℕ = EnumDisc→Retractℕ Yenum Ydisc
  IY : Y → ℕ
  IY = Yretℕ .fst
  RY : ℕ → Opt Y
  RY = Yretℕ .snd .fst
  retY : ∀ y → RY (IY y) ≡ Some y
  retY = Yretℕ .snd .snd


  module _ {P : X → Type} {Q : Y → Type} (redPQ : P ≼₁ Q) (redQP : Q ≼₁ P) where

    private
        _∈₁_ : X → List (X × Y) → Type
        x ∈₁ C = x ∈₁⟨ XYdisc ⟩ C
        _∈₂_ : Y → List (X × Y) → Type
        y ∈₂ C = y ∈₂⟨ XYdisc ⟩ C
        _∈<>_ : (X × Y) → List (X × Y) → Type
        xy ∈<> xys = xy ∈⟨ XYdisc ⟩ xys


        findXY : List (X × Y) → X → Y
        findXY = Find.find XYdisc redPQ
        findYX : List (Y × X) → Y → X
        findYX = Find.find YXdisc redQP

    open isCorrSeq
    open _≼₁_

    mutual

        C'a2 : ∀ x (Cn : List (X × Y)) → Dec (x ∈₁ Cn) → List (X × Y)
        C'a2 x Cn (yes _) = Cn
        C'a2 x Cn (no  _) = (x , findXY Cn x) ∷ Cn

        C'a1 : ℕ → List (X × Y) → Opt X → List (X × Y)
        C'a1 n Cn None = Cn
        C'a1 n Cn (Some x) = C'a2 x Cn (x ∈?₁⟨ XYdisc ⟩ Cn)

        C' : ℕ → List (X × Y)
        C' n = C'a1 n (C n) (RX n)


        Ca2 : ∀ y (C'n : List (X × Y)) → Dec (y ∈₂ C'n) → List (X × Y)
        Ca2 y C'n (yes _) = C'n
        Ca2 y C'n (no  _) = (findYX (swap C'n) y , y) ∷ C'n

        Ca1 : ℕ → List (X × Y) → Opt Y → List (X × Y)
        Ca1 n C'n None  = C'n
        Ca1 n C'n (Some y)  = Ca2 y C'n (y ∈?₂⟨ XYdisc ⟩ C'n)

        C : ℕ → List (X × Y)
        C 0 = []
        C (suc n) = Ca1 n (C' n) (RY n)

    mutual

        C'seq : ∀ n → isCorrSeq (C' n) P Q XYdisc
        C'seq n with RX n
        ... | None  = Cseq n
        ... | Some x with x ∈?₁⟨ XYdisc ⟩ C n
        ... | yes _ = Cseq n
        ... | no ¬xin = Find.spec XYdisc redPQ (Cseq n) ¬xin

        Cseq : ∀ n → isCorrSeq (C n) P Q XYdisc
        Cseq 0 = emptyCS
        Cseq (suc n) with RY n
        ... | None  = C'seq n
        ... | Some y with y ∈?₂⟨ XYdisc ⟩ C' n
        ... | yes _ = C'seq n
        ... | no ¬yin₂ =
            subst (λ l → isCorrSeq l P Q XYdisc)
                (cong ((findYX (swap (C' n)) y , y) ∷_) (swap-inv (C' n)))
            (subst (λ disc → isCorrSeq ((findYX (swap (C' n)) y , y) ∷ (swap (swap (C' n)))) P Q disc)
                (discSwap-inv XYdisc)
            (swap-Cseq (Find.spec (discSwap XYdisc) redQP (swap-Cseq (C'seq n))
                        λ (x , xyins) → ¬yin₂ (x , swap∈ XYdisc (x , y) (C' n) xyins)))
            )


    extend : ∀ {n} {xy} {xys} → xy ∈<> xys → xy ∈<> C'a1 n xys (RX n)
    extend {n} {xy} {xys} xyinC with RX n
    ... | None = xyinC
    ... | Some x with x ∈?₁⟨ XYdisc ⟩ xys
    ... | yes _ = xyinC
    ... | no _ with XYdisc (x , findXY xys x) xy
    ... | yes _ = tt
    ... | no _ = xyinC

    extend' : ∀ {n} {xy} {xys} → xy ∈<> xys → xy ∈<> Ca1 n xys (RY n)
    extend' {n} {xy} {xys} xyinC with RY n
    ... | None = xyinC
    ... | Some y with y ∈?₂⟨ XYdisc ⟩ xys
    ... | yes _ = xyinC
    ... | no _ with XYdisc (findYX (swap xys) y , y) xy
    ... | yes _ = tt
    ... | no _ = xyinC

    extend₁ : ∀ {n} {x} {xys} → x ∈₁ xys → x ∈₁ C'a1 n xys (RX n)
    extend₁ (y , xyin) = y , extend xyin

    extend₂ : ∀ {n} {y} {xys} → y ∈₂ xys → y ∈₂ C'a1 n xys (RX n)
    extend₂ (x , xyin) = x , extend xyin

    extend₁' : ∀ {n} {x} {xys} → x ∈₁ xys → x ∈₁ Ca1 n xys (RY n)
    extend₁' (y , xyin) = y , extend' xyin

    extend₂' : ∀ {n} {y} {xys} → y ∈₂ xys → y ∈₂ Ca1 n xys (RY n)
    extend₂' (x , xyin) = x , extend' xyin

    subC : ∀ {m} {n} {xy} → m ≤ n → xy ∈<> C m → xy ∈<> C n
    subC {n = 0} {xy} m≤0 xyinm = subst (xy ∈<>_ ∘ C) (≤0→≡0 m≤0) xyinm
    subC {suc m} {suc n} {xy} sm≤sn xyinsm with ≤-split sm≤sn
    ... | inr sm=sn = subst (xy ∈<>_ ∘ C) sm=sn xyinsm
    ... | inl sm<sn = extend' (extend (subC (pred-≤-pred sm<sn) xyinsm))

    C'spec-small : ∀ n x → x ∈₁ C'a1 n (C n) (Some x)
    C'spec-small n x with x ∈?₁⟨ XYdisc ⟩ C n
    ... | yes xin = xin
    ... | no _ = findXY (C n) x , help where
        help : (x , findXY (C n) x) ∈<> ((x , findXY (C n) x) ∷ C n)
        help with XYdisc (x , findXY (C n) x) (x , findXY (C n) x)
        ... | yes _ = tt
        ... | no ¬p = ⊥.rec (¬p refl)

    Cspec-small : ∀ n y → y ∈₂ Ca1 n (C' n) (Some y)
    Cspec-small n y with y ∈?₂⟨ XYdisc ⟩ C' n
    ... | yes yin = yin
    ... | no _ = findYX (swap (C' n)) y , help where
        help : (findYX (swap (C' n)) y , y) ∈<> ((findYX (swap (C' n)) y , y) ∷ C' n)
        help with XYdisc (findYX (swap (C' n)) y , y) (findYX (swap (C' n)) y , y)
        ... | yes _ = tt
        ... | no ¬p = ⊥.rec (¬p refl)

    CspecX : ∀ {x} {n} → IX x < n → x ∈₁ C n
    CspecX {x} {zero} Ix<0 = ⊥.rec (¬-<-zero Ix<0)
    CspecX {x} {suc n} Ix<sn with <-split Ix<sn
    ... | inl Ix<n = extend₁' (extend₁ (CspecX Ix<n))
    ... | inr p =
        subst (λ a → x ∈₁ Ca1 n (C'a1 n (C n) (RX a)) (RY n)) p
        (subst (λ a → x ∈₁ Ca1 n (C'a1 n (C n) a) (RY n)) (sym (retX x))
        (extend₁' (C'spec-small n x)))

    CspecY : ∀ {y} {n} → IY y < n → y ∈₂ C n
    CspecY {y} {zero} Iy<0 = ⊥.rec (¬-<-zero Iy<0)
    CspecY {y} {suc n} Iy<sn with <-split Iy<sn
    ... | inl Iy<n = extend₂' (extend₂ (CspecY Iy<n))
    ... | inr p =
        subst (λ a → y ∈₂ Ca1 n (C' n) (RY a)) p
        (subst (λ a → y ∈₂ Ca1 n (C' n) a) (sym (retY y))
        (Cspec-small n y))

    f' : X → Y
    f' x = fst (CspecX {n = suc (IX x)} (0 , refl))

    g' : Y → X
    g' y = fst (CspecY {n = suc (IY y)} (0 , refl))

    f'∘g'-id : section f' g'
    f'∘g'-id y = answer (Dichotomyℕ (suc (IY y)) (suc (IX (g' y)))) where
        yin : (g' y , y) ∈<> C (suc (IY y))
        yin = snd (CspecY (0 , refl))

        g'yin : (g' y , f' (g' y)) ∈<> C (suc (IX (g' y)))
        g'yin = snd (CspecX (0 , refl))

        answer : ((suc (IY y)) ≤ (suc (IX (g' y)))) ⊎ ((suc (IX (g' y))) < (suc (IY y))) → f' (g' y) ≡ y
        answer (inl siy≤sig') =
            Cseq (suc (IX (g' y))) .c2
            (g' y , f' (g' y)) g'yin
            y (subC siy≤sig' yin)
        answer (inr sig'<siy) =
            Cseq (suc (IY y)) .c2
            (g' y , f' (g' y)) (subC (<-weaken sig'<siy) g'yin)
            y yin

    g'∘f'-id : retract f' g'
    g'∘f'-id x = answer (Dichotomyℕ (suc (IX x)) (suc (IY (f' x)))) where
        xin : (x , f' x) ∈<> C (suc (IX x))
        xin = snd (CspecX (0 , refl))

        f'xin : (g' (f' x) , f' x) ∈<> C (suc (IY (f' x)))
        f'xin = snd (CspecY (0 , refl))

        answer : ((suc (IX x)) ≤ (suc (IY (f' x)))) ⊎ ((suc (IY (f' x))) < (suc (IX x))) → g' (f' x) ≡ x
        answer (inl six≤sif') =
            Cseq (suc (IY (f' x))) .c3
            (g' (f' x) , f' x) f'xin
            x (subC six≤sif' xin)
        answer (inr sif<six) =
            Cseq (suc (IX x)) .c3
            (g' (f' x) , f' x) (subC (<-weaken sif<six) f'xin)
            x xin

    IsomorphismTheorem : Σ[ (f , g) ∈ (X → Y) × (Y → X) ]
                            (∀ x → (P x ⇔ Q (f x)) × (g (f x) ≡ x))
                          × (∀ y → (Q y ⇔ P (g y)) × (f (g y) ≡ y))
    IsomorphismTheorem =
        (f' , g') ,
        (λ x →       (Cseq (suc (IX x)) .c1 (x , f' x) (snd (CspecX (0 , refl)))) , g'∘f'-id x) ,
        (λ y → ⇔sym (Cseq (suc (IY y)) .c1 (g' y , y) (snd (CspecY (0 , refl)))) , f'∘g'-id y)



CantorBernstein : ∀ {X Y : Type} {f : X → Y} {g : Y → X} →
                  Enumerable X → Discrete X → Enumerable Y → Discrete Y →
                  isInjective f → isInjective g → Iso X Y
CantorBernstein {X} {Y} {f} {g} eX dX eY dY fInj gInj = iso
    (mh .fst .fst) (mh .fst .snd) (λ y → mh .snd .snd y .snd) (λ x → mh .snd .fst x .snd) where
        P : X → Type
        P x = ⊥
        Q : Y → Type
        Q y = ⊥

        redPQ : P ≼₁ Q
        redPQ = record { fun = f ; Px⇔Qfx = λ _ → (λ ()) , (λ ()) ; funInj = fInj }
        redQP : Q ≼₁ P
        redQP = record { fun = g ; Px⇔Qfx = λ _ → (λ ()) , (λ ()) ; funInj = gInj }

        mh : Σ[ (f , g) ∈ (X → Y) × (Y → X) ]
                (∀ x → (P x ⇔ Q (f x)) × (g (f x) ≡ x))
              × (∀ y → (Q y ⇔ P (g y)) × (f (g y) ≡ y))
        mh = Myhill.IsomorphismTheorem eX eY dX dY redPQ redQP

CantorBernstein-ret : ∀ {X Y : Type} {f : X → Y} {g : Y → X} →
                  X isRetractOf ℕ → Y isRetractOf ℕ →
                  isInjective f → isInjective g → Iso X Y
CantorBernstein-ret Xretℕ Yretℕ =
    CantorBernstein
    (retract-pres-enum Xretℕ enumℕ) (retract-pres-discrete Xretℕ discreteℕ)
    (retract-pres-enum Yretℕ enumℕ) (retract-pres-discrete Yretℕ discreteℕ)
