{-# OPTIONS --safe #-}

module Automata.EQRelation where

open import Automata.Imports
open import Cubical.HITs.SetQuotients renaming ( [_] to class ) public

Relation : {ℓ ℓ' : Level} → (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Relation {ℓ' = ℓ'} A = A → A → Type ℓ'


record is-EQ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor EQ
    field
        rrefl : ∀ {x} → R x x
        rsym : ∀ {x y} → R x y → R y x
        rtrans : ∀ {x y z} → R x y → R y z → R x z
open is-EQ

path-EQ : {ℓ ℓ' : Level} {A : Type ℓ} (R : A → A → Type ℓ') →
          (∀ x y → R x y → x ≡ y) → (∀ x y → x ≡ y → R x y) →
          is-EQ R
path-EQ R rp pr = EQ
    (pr _ _ refl)
    (λ Rxy → pr _ _ (sym (rp _ _ Rxy)))
    (λ Rxy Ryz → pr _ _ (rp _ _ Rxy ∙ rp _ _ Ryz))

EQRel : {ℓ ℓ' : Level} → (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EQRel {ℓ} {ℓ'} A = Σ (Relation {ℓ} {ℓ'} A) is-EQ

_//_ : {ℓ ℓ' : Level} (A : Type ℓ) (E : EQRel {ℓ} {ℓ'} A) → Type (ℓ-max ℓ ℓ')
A // E = A / (E .fst)


