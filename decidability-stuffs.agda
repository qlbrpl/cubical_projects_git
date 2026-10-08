{-# OPTIONS --safe #-}

module decidability-stuffs where

open import Preamble
open import Cubical.Data.Fin renaming (any? to check-any)
open import Cubical.Data.Empty as ⊥


DecStable : ∀ {A : Type} → Dec A → Stable A
DecStable DecA nnA with DecA
...     | yes a = a
...     | no nA = ⊥.rec (nnA nA)

Adec→nAdec : ∀ {A : Type} → Dec A → Dec (¬ A)
Adec→nAdec decA with decA
...     | yes a = no (λ f → f a)
...     | no nA = yes nA

DecℕDepFunc : {P : ℕ → Type} → (n : ℕ) →
                (∀ ((d , d<n) : Fin n) → Dec (P d)) →
                Dec (∀ ((d , d<n) : Fin n) → P d)
DecℕDepFunc {P} n Pdec with (check-any nPdec)
    where
        nPdec : ∀ ((d , d<n) : Fin n) → Dec (¬ (P d))
        nPdec x = Adec→nAdec (Pdec x)
... | yes (failpt , fails) = no (λ f → fails (f failpt))
... | no No-finD-SuchThat-NotPd = yes (λ a → nnelim a (λ nPa → No-finD-SuchThat-NotPd (a , nPa)))
    where
        nnelim : (∀ ((d , d<n) : Fin n) → ¬ ¬ (P d) → P d)
        nnelim d = DecStable (Pdec d)

DecFunc : ∀ {A B : Type} → Dec A → Dec B → Dec (A → B)
DecFunc (yes a) (yes b) = yes λ _ → b
DecFunc (yes a) (no nB) = no (λ f → nB (f a))
DecFunc (no nA) _       = yes λ a → ⊥.rec (nA a)
