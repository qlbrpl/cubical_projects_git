{-# OPTIONS --safe #-}

module Preamble where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Isomorphism renaming ( Iso to _≅_ ) public

open import Cubical.Data.Empty as ⊥ hiding (elim) public
open import Cubical.Data.Unit renaming ( Unit to ⊤ ) public
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat hiding (elim) public
open import Cubical.Data.List hiding ( elim ; rec ) public
open import Cubical.Data.Bool.Base hiding ( _≟_ ) public
open import Cubical.Data.Sum hiding (elim ; rec ; map) public
open import Cubical.Relation.Nullary public


private
    variable
        ℓ ℓ' : Level

step⇒ : {A : Type ℓ} (B : Type ℓ') → (A → B) → A → B
step⇒ _ f = f

step⇒⟨⟩ : (A : Type ℓ) → A → A
step⇒⟨⟩ A a = a

syntax step⇒ B f x = x ⇒⟨ f ⟩ B

syntax step⇒⟨⟩ A a = a ⇒⟨⟩ A

infixl -9 step⇒ step⇒⟨⟩

-- (bad) example usage
private
    add≡ : ∀ {a} {b} n → a ≡ b → (n + a) ≡ (n + b)
    add≡ zero p = p
    add≡ {a} {b} (suc n) p =
        p :>                      a ≡ b
        ⇒⟨ add≡ n ⟩         (n + a) ≡ (n + b)
        ⇒⟨ cong suc ⟩   suc (n + a) ≡ suc (n + b)
        ⇒⟨⟩             (suc n) + a ≡ (suc n) + b

data All {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  []  :                             All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
