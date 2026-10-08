{-# OPTIONS --safe #-}

module MyhillCB.Remove where

open import MyhillCB.Imports
open import MyhillCB.Base
open import Cubical.Data.Empty as ⊥

remove-aux : {X : Type} → (P : X → Type) → (x : X) → Dec (P x) → List X → List X
remove-aux _ x (yes _) xs = xs
remove-aux _ x (no  _) xs = x ∷ xs

remove : {X : Type} → (P : X → Type) → (∀ x → Dec (P x)) → List X → List X
remove P Pdec [] = []
remove P Pdec (x ∷ xs) = remove-aux P x (Pdec x) (remove P Pdec xs)

remove≤ : {X : Type} → (P : X → Type) → (Pdec : ∀ x → Dec (P x)) → (xs : List X) →
          length (remove P Pdec xs) ≤ length xs
remove≤ P Pdec [] = 0 , refl
remove≤ P Pdec (x ∷ xs) with Pdec x
... | no  _ = suc-≤-suc (remove≤ P Pdec xs)
... | yes _ = ≤-trans (remove≤ P Pdec xs) (1 , refl)

remove< : {X : Type} → (P : X → Type) → (Pdec : ∀ x → Dec (P x)) → (xs : List X) →
          (Xdisc : Discrete X) → {x : X} → x ∈⟨ Xdisc ⟩ xs → (Px : P x) →
          length (remove P Pdec xs) < length xs
remove< P Pdec (x' ∷ xs) Xdisc {x} xin Px with Pdec x'
... | yes _ = suc-≤-suc (remove≤ P Pdec xs)
... | no  ¬p with Xdisc x' x
... | yes x'=x = ⊥.rec (¬p (subst P (sym x'=x) Px))
... | no  _ = suc-≤-suc (remove< P Pdec xs Xdisc xin Px)

remove∈ : {X : Type} → (P : X → Type) → (Pdec : ∀ x → Dec (P x)) →
           (xs : List X) → (Xdisc : Discrete X) → {x : X} →
           x ∈⟨ Xdisc ⟩ (remove P Pdec xs) → x ∈⟨ Xdisc ⟩ xs
remove∈ P Pdec (x' ∷ xs) Xdisc {x} xinr with Xdisc x' x | Pdec x'
... | yes _ | _ = tt
... | no  _ | yes _ = remove∈ P Pdec xs Xdisc {x} xinr
... | no ¬p | no ¬Px' = remove∈ P Pdec xs Xdisc {x} xinr' where
    xinr' : x ∈⟨ Xdisc ⟩ remove P Pdec xs
    xinr' with Xdisc x' x
    ... | yes p = ⊥.rec (¬p p)
    ... | no  _ = xinr

∉remove : {X : Type} → (P : X → Type) → (Pdec : ∀ x → Dec (P x)) →
           (xs : List X) → (Xdisc : Discrete X) → {x : X} →
           P x → ¬ (x ∈⟨ Xdisc ⟩ (remove P Pdec xs))
∉remove P Pdec (x' ∷ xs) Xdisc {x} Px xin with Pdec x'
... | yes _ = ∉remove P Pdec xs Xdisc Px xin
... | no ¬Px' with Xdisc x' x
... | yes p = ¬Px' (subst P (sym p) Px)
... | no ¬p = ∉remove P Pdec xs Xdisc Px xin

∈remove : {X : Type} → (P : X → Type) → (Pdec : ∀ x → Dec (P x)) →
           (xs : List X) → (Xdisc : Discrete X) → {x : X} →
           ¬ (P x) → x ∈⟨ Xdisc ⟩ xs → x ∈⟨ Xdisc ⟩ (remove P Pdec xs)
∈remove P Pdec (x' ∷ xs) Xdisc {x} ¬Px xin with Pdec x'
... | yes Px' with Xdisc x' x
... | yes p = ⊥.rec (¬Px (subst P p Px'))
... | no ¬p = ∈remove P Pdec xs Xdisc ¬Px xin
∈remove P Pdec (x' ∷ xs) Xdisc {x} ¬Px xin | no ¬Px' with Xdisc x' x
... | yes p = tt
... | no ¬p = ∈remove P Pdec xs Xdisc ¬Px xin

open isCorrSeq
removeCorrSeq : {X Y : Type} {P : X → Type} {Q : Y → Type} {C : List (X × Y)} {XYdisc : Discrete (X × Y)}
                (R : (X × Y) → Type) (Rdec : ∀ xy → Dec (R xy)) →
                isCorrSeq C P Q XYdisc → isCorrSeq (remove R Rdec C) P Q XYdisc
removeCorrSeq {C = C} {XYdisc} R Rdec CS .c1 xy xyinr =
    CS .c1 xy (remove∈ R Rdec C XYdisc xyinr)
removeCorrSeq {C = C} {XYdisc} R Rdec CS .c2 (x , y) xyinr y' xy'inr =
    CS .c2 (x , y) (remove∈ R Rdec C XYdisc xyinr) y' (remove∈ R Rdec C XYdisc xy'inr)
removeCorrSeq {C = C} {XYdisc} R Rdec CS .c3 (x , y) xyinr x' x'yinr =
    CS .c3 (x , y) (remove∈ R Rdec C XYdisc xyinr) x' (remove∈ R Rdec C XYdisc x'yinr)
