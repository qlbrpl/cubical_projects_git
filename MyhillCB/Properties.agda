{-# OPTIONS --safe #-}

module MyhillCB.Properties where

open import MyhillCB.Imports
open import MyhillCB.Base
open import MyhillCB.Least
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Bool.Properties using (isSetBool)


optSet : {X : Type} → isSet X → isSet (Opt X)
optSet setX = subst isSet (sym opt≡sum) (isSet⊎ setX isSetUnit)

someInj : {X : Type} → isInjective {X = X} Some
someInj p = lower (⊎Path.encode (inl _) (inl _) (cong opt→sum p))

optDisc : {X : Type} → Discrete X → Discrete (Opt X)
optDisc _ None None = yes refl
optDisc _ None (Some _) = no none≠some
optDisc _ (Some _) None = no (none≠some ∘ sym)
optDisc discX (Some x) (Some x') with discX x x'
... | yes p = yes (cong Some p)
... | no ¬p = no (λ p → ¬p (someInj p))

retraction-injective : {X : Type} {Y : Type} → ((f , _) : X isRetractOf Y) → isInjective f
retraction-injective (f , g , ret) p = someInj (sym (ret _) ∙ cong g p ∙ ret _)

retract-pres-discrete : {X : Type} {Y : Type} → X isRetractOf Y → Discrete Y → Discrete X
retract-pres-discrete (f , g , ret) discY x1 x2 with discY (f x1) (f x2)
... | yes p = yes (someInj (sym (ret x1) ∙ cong g p ∙ ret x2))
... | no ¬p = no (¬p ∘ cong f)

retract-pres-enum : {X : Type} {Y : Type} → X isRetractOf Y → Enumerable Y → Enumerable X
retract-pres-enum (f , g , ret) (enumY , surjY) = enumX , surjX where
    enumX-aux : Opt _ → Opt _
    enumX-aux (Some y) = g y
    enumX-aux None = None

    enumX : ℕ → Opt _
    enumX n = enumX-aux (enumY n)

    surjXrec : ∀ x → Σ[ n ∈ ℕ ] enumY n ≡ Some (f x) → ∃[ n ∈ ℕ ] enumX n ≡ Some x
    surjXrec x (n , p) = ∣ n , subst (λ q → enumX-aux q ≡ Some x) (sym p) (ret x) ∣₁

    surjX : ∀ x → ∃[ n ∈ ℕ ] enumX n ≡ Some x
    surjX x = PT.rec squash₁ (surjXrec x) (surjY (f x))

lemma24 : {X : Type} {Y : Type} (F : X → Y → 𝔹) → Enumerable Y → isSet Y →
          (∀ x → ∃[ y ∈ Y ] F x y ≡ true) → (Σ[ G ∈ (X → Y) ] ∀ x → F x (G x) ≡ true)
lemma24 {X} {Y} F (enumY , surjY) setY f = fst ∘ getPx , snd ∘ snd ∘ getPx where

    P : X → ℕ → Type
    P x n = Σ[ y ∈ Y ] (enumY n ≡ Some y) × (F x y ≡ true)

    lem1 : ∀ x → ∃[ n ∈ ℕ ] P x n
    lem1 x = PT.rec squash₁ lem1a (f x) where
        lem1a : Σ[ y ∈ Y ] F x y ≡ true → ∃[ n ∈ ℕ ] Σ[ y ∈ Y ] ((enumY n ≡ Some y) × (F x y ≡ true))
        lem1a (y , p1) = PT.rec squash₁ lem1b (surjY y) where
            lem1b : Σ[ n ∈ ℕ ] (enumY n ≡ Some y) → ∃[ n ∈ ℕ ] Σ[ y' ∈ Y ] (enumY n ≡ Some y') × (F x y' ≡ true)
            lem1b (n , p2) = ∣ n , y , p2 , p1 ∣₁

    Pdec : ∀ x n → Dec (P x n)
    Pdec x n with enumY n
    ... | None = no (none≠some ∘ fst ∘ snd)
    ... | Some y with Bcomp (F x y) true
    ... | yes p = yes (y , refl , p)
    ... | no ¬p = no (λ (y' , sy=sy' , p) → ¬p (subst (λ a → F x a ≡ true) (sym (someInj sy=sy')) p))

    Pprop : ∀ x n → isProp (P x n)
    Pprop x n (y , p1 , p2) (y' , p1' , p2') =
        ΣPathP (someInj (sym p1 ∙ p1') ,
        ΣPathP (isProp→PathP (λ i → optSet setY _ _) _ _ ,
        isProp→PathP (λ i → isSetBool _ _) _ _))

    chooseBig : (x : X) → Σ[ n ∈ ℕ ] (P x n) × _
    chooseBig x = findLeast-prop (Pdec x) (Pprop x) (lem1 x)

    getPx : (x : X) → P x (chooseBig x .fst)
    getPx = fst ∘ snd ∘ chooseBig

indexLeast : {X : Type} → ((enum , surj) : Enumerable X) → Discrete X →
             ∀ x → Σ[ n ∈ ℕ ] ((enum n ≡ Some x) × (∀ m → enum m ≡ Some x → n ≤ m))
indexLeast (enum , surj) discX x =
    findLeast-prop (λ a → optDisc discX _ _) (λ a → Discrete→isSet (optDisc discX) _ _) (surj x)

EnumDisc→Retractℕ : {X : Type} → Enumerable X → Discrete X → X isRetractOf ℕ
EnumDisc→Retractℕ enumX@(enum , surj) discX =
    fst ∘ (indexLeast enumX discX) , enum , fst ∘ snd ∘ (indexLeast enumX discX)

discSwap-inv : {X Y : Type} → (XYdisc : Discrete (X × Y)) → discSwap (discSwap XYdisc) ≡ XYdisc
discSwap-inv XYdisc = funExt (funExt ∘ answer) where
    answer : ∀ xy1 xy2 → discSwap (discSwap XYdisc) xy1 xy2 ≡ XYdisc xy1 xy2
    answer xy1 xy2 with discSwap (discSwap XYdisc) xy1 xy2 | XYdisc xy1 xy2
    ... | yes p | no ¬q = ⊥.rec (¬q p)
    ... | no ¬p | yes q = ⊥.rec (¬p q)
    ... | yes p | yes q = refl
    ... | no ¬p | no ¬q = refl

swap-inv : {X Y : Type} → (xys : List (X × Y)) → swap (swap xys) ≡ xys
swap-inv [] = refl
swap-inv (xy ∷ xys) = ListPath.decode (swap (swap (xy ∷ xys))) (xy ∷ xys)
                      (refl , ListPath.encode (swap (swap xys)) xys (swap-inv xys))

∈cons : {X : Type} {x x' : X} → ∀ Xdisc xs → x ∈⟨ Xdisc ⟩ xs → x ∈⟨ Xdisc ⟩ (x' ∷ xs)
∈cons {x = x} {x'} Xdisc xs xin' with Xdisc x' x
... | yes _ = tt
... | no _ = xin'

∈swap : ∀ {X Y : Type} XYdisc ((x , y) : X × Y) xys → (x , y) ∈⟨ XYdisc ⟩ xys → (y , x) ∈⟨ discSwap XYdisc ⟩ swap xys
∈swap XYdisc xy@(x , y) ((x' , y') ∷ xys) xyin' with (discSwap XYdisc) (y' , x') (y , x)
... | yes _ = tt
... | no ¬p = ∈swap XYdisc (x , y) xys xyin where
    xyin : xy ∈⟨ XYdisc ⟩ xys
    xyin with XYdisc (x' , y') xy
    ... | no _ = xyin'
    ... | yes p = ⊥.rec (¬p (ΣPathP (PathPΣ p .snd , PathPΣ p .fst)))

swap∈ : ∀ {X Y : Type} XYdisc ((x , y) : X × Y) xys → (y , x) ∈⟨ discSwap XYdisc ⟩ swap xys → (x , y) ∈⟨ XYdisc ⟩ xys
swap∈ XYdisc xy@(x , y) ((x' , y') ∷ xys) yxin' with XYdisc (x' , y') (x , y)
... | yes _ = tt
... | no ¬p = swap∈ XYdisc (x , y) xys yxin'


allCons : {X : Type} {P : X → Type} (xs : List X) → ∀ {x'} Xdisc →
          P x' → (∀ x → x ∈⟨ Xdisc ⟩ xs → P x) → (∀ x → x ∈⟨ Xdisc ⟩ (x' ∷ xs) → P x)
allCons _ {x'} Xdisc Px' allxs x xin' with Xdisc x' x
... | yes p = subst _ p Px'
... | no _ = allxs x xin'

open isCorrSeq

emptyCS : ∀ {X Y : Type} {P : X → Type} {Q : Y → Type} {XYdisc} →
            isCorrSeq [] P Q XYdisc
emptyCS .c1 _ ()
emptyCS .c2 _ ()
emptyCS .c3 _ ()

module _ {X Y : Type} {P : X → Type} {Q : Y → Type} {XYdisc : Discrete (X × Y)} where
    private
        YXdisc : Discrete (Y × X)
        YXdisc = discSwap XYdisc


    tail-Cseq : ∀ {C} {xy} → isCorrSeq (xy ∷ C) P Q XYdisc → isCorrSeq C P Q XYdisc
    tail-Cseq {C} {x , y} C'seq .c1 xy xyin = C'seq .c1 xy (∈cons XYdisc C xyin)
    tail-Cseq {C} {x , y} C'seq .c2 xy xyin y' xy'in = C'seq .c2 xy (∈cons XYdisc C xyin) y' (∈cons XYdisc C xy'in)
    tail-Cseq {C} {x , y} C'seq .c3 xy xyin x' x'yin = C'seq .c3 xy (∈cons XYdisc C xyin) x' (∈cons XYdisc C x'yin)

    swap-Cseq : ∀ {C} → isCorrSeq C P Q XYdisc → isCorrSeq (swap C) Q P YXdisc
    swap-Cseq {[]} Cseq = emptyCS
    swap-Cseq {(x , y) ∷ C} Cseq = output where
        output : isCorrSeq ((y , x) ∷ swap C) Q P YXdisc
        output .c1 (y' , x') y'x'ins = snd sol , fst sol where
            sol = Cseq .c1 (x' , y') (swap∈ XYdisc (x' , y') ((x , y) ∷ C) y'x'ins)
        output .c2 (y1 , x1) y1x1ins x' y1x'ins = Cseq .c3
            (x1 , y1) (swap∈ XYdisc (x1 , y1) ((x , y) ∷ C) y1x1ins)
            x' (swap∈ XYdisc (x' , y1) ((x , y) ∷ C) y1x'ins)
        output .c3 (y1 , x1) y1x1ins y' y'x1ins = Cseq .c2
            (x1 , y1) (swap∈ XYdisc (x1 , y1) ((x , y) ∷ C) y1x1ins)
            y' (swap∈ XYdisc (x1 , y') ((x , y) ∷ C) y'x1ins)
