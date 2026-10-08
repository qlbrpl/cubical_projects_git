{-# OPTIONS --safe #-}

module MyhillCB.Least where

open import MyhillCB.Imports
open import MyhillCB.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT


funcProp : {A : Type} {B : A → Type} → (∀ a → isProp (B a)) → isProp (∀ a → B a)
funcProp BProp f g = funExt (λ x → BProp x (f x) (g x))

findLeast-worker :
        {n : ℕ} →
            ({x : ℕ} → (x < n) → {P : ℕ → Type} → P x → (∀ a → Dec (P a)) →
            Σ[ l ∈ ℕ ] (P l) × (∀ z → P z → l ≤ z)) →
        {P : ℕ → Type} → P n → (∀ a → Dec (P a)) →
        Σ[ l ∈ ℕ ] (P l) × (∀ z → P z → l ≤ z)
findLeast-worker {n = zero} IH P0 Pdec = zero , (P0 , (λ _ _ → zero-≤))
findLeast-worker {n = n@(suc n-1)} IH {P = P} Pn Pdec with any? {n = n} Qdec where
    Qdec : ∀ ((x , x<n) : Fin n) → Dec (P x)
    Qdec (x , x<n) = Pdec x
... | yes ((x , x<n) , Px) = IH x<n Px Pdec
... | no ¬x,x<n,Px = n , Pn , l where
        l : ∀ x → P x → n ≤ x
        l x Px with (Dichotomyℕ n x)
        ... | inl n≤x = n≤x
        ... | inr x<n = ⊥.rec (¬x,x<n,Px ((x , x<n) , Px))

findLeast-explicit : (n : ℕ) → (P : ℕ → Type) → P n → (∀ a → Dec (P a)) →
                     Σ[ l ∈ ℕ ] (P l) × (∀ z → P z → l ≤ z)
findLeast-explicit = WFI.induction <-wellfounded
                     (λ n rec P → findLeast-worker {n = n} (λ {x} x<n {P} → rec x x<n P) {P})

findLeast-untrunc : {n : ℕ} → {P : ℕ → Type} → P n → (∀ a → Dec (P a)) →
                    Σ[ l ∈ ℕ ] (P l) × (∀ z → P z → l ≤ z)
findLeast-untrunc {n = n} {P = P} = findLeast-explicit n P

findLeast-prop : {P : ℕ → Type} → (∀ a → Dec (P a)) → (∀ a → isProp (P a)) →
                 ∃ ℕ P → Σ[ n ∈ ℕ ] ((P n) × (∀ z → P z → n ≤ z))
findLeast-prop {P} Pdec Pprop = PT.rec lem λ (m , Pm) → findLeast-untrunc Pm Pdec where
    lem : isProp (Σ[ n ∈ ℕ ] ((P n) × (∀ z → P z → n ≤ z)) )
    lem (n , Pn , ln) (n' , Pn' , ln') =
        ΣPathP (≤-antisym (ln n' Pn') (ln' n Pn) ,
        ΣPathP (isProp→PathP (λ i → Pprop _) _ _ ,
        isProp→PathP (λ i → funcProp (λ _ → funcProp λ _ → isProp≤)) _ _))
