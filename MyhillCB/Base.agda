{-# OPTIONS --safe #-}

module MyhillCB.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit renaming ( Unit to ⊤ )
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.List as L
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; rec ; map)
open import Cubical.HITs.PropositionalTruncation as PT hiding (map2)
open import Cubical.Relation.Nullary


data Opt (X : Type) : Type where
    None : Opt X
    Some : X → Opt X

none≠some : {X : Type} {x : X} → ¬ None ≡ Some x
none≠some n=sx = subst caseOpt (sym n=sx) tt where
    caseOpt : {X : Type} → Opt X → Type
    caseOpt (Some x) = ⊤
    caseOpt None = ⊥

opt→sum : {X : Type} → Opt X → (X ⊎ ⊤)
opt→sum (Some x) = inl x
opt→sum None = inr tt

sum→opt : {X : Type} → (X ⊎ ⊤) → Opt X
sum→opt (inl x) = Some x
sum→opt (inr .tt) = None

opt≡sum : {X : Type} → Opt X ≡ (X ⊎ ⊤)
opt≡sum = isoToPath (iso opt→sum sum→opt rinv linv) where
    rinv : section opt→sum sum→opt
    rinv (inl _) = refl
    rinv (inr _) = refl
    linv : retract opt→sum sum→opt
    linv (Some _) = refl
    linv None = refl

Enumerable : (X : Type) → Type
Enumerable X = Σ[ f ∈ (ℕ → Opt X) ] ∀ x → ∃[ n ∈ ℕ ] f n ≡ Some x

enumℕ : Enumerable ℕ
enumℕ = Some , λ x → ∣ x , refl ∣₁

discℕ : Discrete ℕ
discℕ = discreteℕ

_isRetractOf_ : (X Y : Type) → Type
X isRetractOf Y = Σ[ f ∈ (X → Y) ] Σ[ g ∈ (Y → Opt X) ] (∀ x → g (f x) ≡ Some x)

isInjective : {X Y : Type} (f : X → Y) → Type
isInjective f = ∀ {x1} {x2} → (f x1) ≡ (f x2) → x1 ≡ x2


_⇔_ : Type → Type → Type
P ⇔ Q = (P → Q) × (Q → P)

_⊚_ : {X Y Z : Type} → X ⇔ Y → Y ⇔ Z → X ⇔ Z
(xy , yx) ⊚ (yz , zy) = (yz ∘ xy , yx ∘ zy)

⇔sym : {X Y : Type} → X ⇔ Y → Y ⇔ X
⇔sym (XY , YX) = YX , XY


∈-aux : {X : Type} {x x' : X} → Dec (x' ≡ x) → Type → Type
∈-aux (yes _) t = ⊤
∈-aux (no  _) t = t

_∈⟨_⟩_ : {X : Type} → X → Discrete X → List X → Type
_ ∈⟨ _ ⟩ [] = ⊥
x ∈⟨ Xdisc ⟩ (x' ∷ xs) = ∈-aux (Xdisc x' x) (x ∈⟨ Xdisc ⟩ xs)

_∈₁⟨_⟩_ : {X Y : Type} → X → Discrete (X × Y) → List (X × Y) → Type
x ∈₁⟨ XYdisc ⟩ C = Σ _ (λ y → (x , y) ∈⟨ XYdisc ⟩ C)

_∈₂⟨_⟩_ : {X Y : Type} → Y → Discrete (X × Y) → List (X × Y) → Type
y ∈₂⟨ XYdisc ⟩ C = Σ _ (λ x → (x , y) ∈⟨ XYdisc ⟩ C)


∈₁-aux : {X : Type} {Y : Type} (x' x : X) (y : Y) → (XYdisc : Discrete (X × Y)) →
         (xys : List (X × Y)) → (pxy : Dec ((x' , y) ≡ (x , y))) → pxy ≡ XYdisc (x' , y) (x , y) →
         Dec (x ∈₁⟨ XYdisc ⟩ xys) →
         Dec (x ∈₁⟨ XYdisc ⟩ ((x' , y) ∷ xys))
∈₁-aux x' x y XYdisc xys (yes _) p _ = yes (y , subst (λ p' → ∈-aux p' ((x , y) ∈⟨ XYdisc ⟩ xys)) p tt)
∈₁-aux x' x y XYdisc xys (no _) _ (yes (y' , xyin)) = yes (y' , answer) where
    answer : ∈-aux (XYdisc (x' , y) (x , y')) ((x , y') ∈⟨ XYdisc ⟩ xys)
    answer with XYdisc (x' , y) (x , y')
    ... | yes _ = tt
    ... | no  _ = xyin
∈₁-aux x' x y XYdisc xys (no ¬p1) p (no ¬p2) = no answer where
    answer : ¬ (Σ[ y' ∈ _ ] (x , y') ∈⟨ XYdisc ⟩ ((x' , y) ∷ xys))
    answer (y' , xy'in) with XYdisc (x' , y) (x , y')
    ... | yes xy'=x'y = ¬p1 (ΣPathP (fst (PathPΣ xy'=x'y) , refl))
    ... | no  _ = ¬p2 (y' , xy'in)

_∈?₁⟨_⟩_ : {X : Type} {Y : Type} → (x : X) → (XYdisc : Discrete (X × Y)) → (xys : List (X × Y)) →
          Dec (x ∈₁⟨ XYdisc ⟩ xys)
x ∈?₁⟨ Xdisc ⟩ [] = no λ ()
x ∈?₁⟨ Xdisc ⟩ ((x' , y) ∷ xys) = ∈₁-aux x' x y Xdisc xys (Xdisc (x' , y) (x , y)) refl (x ∈?₁⟨ Xdisc ⟩ xys)


∈₂-aux : {X : Type} {Y : Type} (y' y : Y) (x : X) → (XYdisc : Discrete (X × Y)) →
         (xys : List (X × Y)) → (pxy : Dec ((x , y') ≡ (x , y))) → pxy ≡ XYdisc (x , y') (x , y) →
         Dec (y ∈₂⟨ XYdisc ⟩ xys) →
         Dec (y ∈₂⟨ XYdisc ⟩ ((x , y') ∷ xys))
∈₂-aux y' y x XYdisc xys (yes _) p _ = yes (x , subst (λ p' → ∈-aux p' ((x , y) ∈⟨ XYdisc ⟩ xys)) p tt)
∈₂-aux y' y x XYdisc xys (no _) _ (yes (x' , xyin)) = yes (x' , answer) where
    answer : ∈-aux (XYdisc (x , y') (x' , y)) ((x' , y) ∈⟨ XYdisc ⟩ xys)
    answer with XYdisc (x , y') (x' , y)
    ... | yes _ = tt
    ... | no  _ = xyin
∈₂-aux y' y x XYdisc xys (no ¬p1) p (no ¬p2) = no answer where
    answer : ¬ (Σ[ x' ∈ _ ] (x' , y) ∈⟨ XYdisc ⟩ ((x , y') ∷ xys))
    answer (x' , x'yin) with XYdisc (x , y') (x' , y)
    ... | yes x'y=xy' = ¬p1 (ΣPathP (refl , snd (PathPΣ x'y=xy')))
    ... | no  _ = ¬p2 (x' , x'yin)

_∈?₂⟨_⟩_ : {X : Type} {Y : Type} → (y : Y) → (XYdisc : Discrete (X × Y)) → (xys : List (X × Y)) →
          Dec (y ∈₂⟨ XYdisc ⟩ xys)
y ∈?₂⟨ Xdisc ⟩ [] = no λ ()
y ∈?₂⟨ Xdisc ⟩ ((x , y') ∷ xys) = ∈₂-aux y' y x Xdisc xys (Xdisc (x , y') (x , y)) refl (y ∈?₂⟨ Xdisc ⟩ xys)

discProd : {X Y : Type} → Discrete X → Discrete Y → Discrete (X × Y)
discProd Xdisc Ydisc (x , y) (x' , y') with Xdisc x x' | Ydisc y y'
... | no ¬px | _ = no (λ p → ¬px (fst (PathPΣ p)))
... | yes px | no ¬py = no (λ p → ¬py (snd (PathPΣ p)))
... | yes px | yes py = yes (ΣPathP (px , py))

discSwap : {X Y : Type} → Discrete (X × Y) → Discrete (Y × X)
discSwap XYdisc (y , x) (y' , x') with XYdisc (x , y) (x' , y')
... | yes p = yes (ΣPathP (PathPΣ p .snd , PathPΣ p .fst))
... | no ¬p = no λ p → ¬p (ΣPathP (PathPΣ p .snd , PathPΣ p .fst))


record _≼₁_ {X Y : Type} (P : X → Type) (Q : Y → Type) : Type where
    no-eta-equality
    field
        fun : X → Y
        Px⇔Qfx : ∀ x → (P x) ⇔ (Q (fun x))
        funInj : isInjective fun

record isCorrSeq {X Y : Type} (C : List (X × Y)) (P : X → Type) (Q : Y → Type)
                 (XYdiscrete : Discrete (X × Y)) : Type where
    no-eta-equality
    field
        c1 : ∀ ((a , b) : X × Y) → (a , b) ∈⟨ XYdiscrete ⟩ C →
                          P a ⇔ Q b
        c2 : ∀ ((a , b) : X × Y) → (a , b) ∈⟨ XYdiscrete ⟩ C →
                          ∀ b' → (a  , b') ∈⟨ XYdiscrete ⟩ C → b ≡ b'
        c3 : ∀ ((a , b) : X × Y) → (a , b) ∈⟨ XYdiscrete ⟩ C →
                          ∀ a' → (a'  , b) ∈⟨ XYdiscrete ⟩ C → a ≡ a'

swap : ∀ {X Y : Type} → List (X × Y) → List (Y × X)
swap = L.map (λ xy → xy .snd , xy .fst)
