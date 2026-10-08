module Book.pg248 where

open import Preamble renaming (Unit to 𝟙)
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Bool renaming (Bool to 𝟚)
-- open import Cubical.Data.Sum.Properties

private
    variable
        ℓ ℓ' : Level


ptd : (ℓ : Level) → Type (ℓ-suc ℓ)
ptd ℓ = Σ[ A ∈ Type ℓ ] A

Map* : ptd ℓ → ptd ℓ' → Type (ℓ-max ℓ ℓ')
Map* (A , a0) (B , b0) = Σ[ f ∈ (A → B) ] f a0 ≡ b0

_+1 : Type ℓ → ptd ℓ
A +1 = A ⊎ 𝟙 , inr tt


Lemma653 : (A : Type ℓ) ((B , b0) : ptd ℓ') → (Map* (A +1) (B , b0)) ≡ (A → B)
Lemma653 A (B , b0) = isoToPath (iso (fun b0) (inv b0) (Rinv b0) (Linv b0)) where

    fun : ∀ b → Map* (A +1) (B , b) → A → B
    fun b (f , p) a = f (inl a)

    inv : ∀ b → (A → B) → Map* (A +1) (B , b)
    inv b g = g+ , refl where
        g+ : ((A +1) .fst) → B
        g+ (inl a) = g a
        g+ (inr .tt) = b

    Rinv : ∀ b → section (fun b) (inv b)
    Rinv b g = refl

    Linv : ∀ b → retract (fun b) (inv b)
    Linv b (f , p) = J (λ b' p' → inv b' (fun b' (f , p')) ≡ (f , p')) 
                       (ΣPathP (funExt reason , refl)) p where
        reason : (x : A ⊎ 𝟙) → fst (inv (f ((A +1) .snd)) (fun (f ((A +1) .snd)) (f , refl))) x ≡ f x
        reason (inl a) = refl
        reason (inr .tt) = refl

𝟚≡𝟙+𝟙 : 𝟚 ≡ 𝟙 ⊎ 𝟙
𝟚≡𝟙+𝟙 = isoToPath (iso fun inv Rinv Linv) where
    fun : 𝟚 → 𝟙 ⊎ 𝟙
    fun false = inl tt
    fun true = inr tt

    inv : 𝟙 ⊎ 𝟙 → 𝟚
    inv (inl .tt) = false
    inv (inr .tt) = true

    Rinv : section fun inv
    Rinv (inl .tt) = refl
    Rinv (inr .tt) = refl

    Linv : retract fun inv
    Linv false = refl
    Linv true = refl

𝟙→B≡B : (B : Type ℓ) → (𝟙 → B) ≡ B
𝟙→B≡B B = isoToPath (iso (λ f → f tt) (λ b tt → b) (λ _ → refl) (λ _ → refl))

Map*𝟚B≡B : ((B , b0) : ptd ℓ) → Map* (𝟚 , true) (B , b0) ≡ B
Map*𝟚B≡B (B  , b0) =  cong (λ x → Map* x (B , b0)) (ΣPathP (𝟚≡𝟙+𝟙 , toPathP refl))
                   ∙∙ Lemma653 𝟙 (B , b0)
                   ∙∙ 𝟙→B≡B B
