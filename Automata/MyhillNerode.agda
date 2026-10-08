{-# OPTIONS --safe #-}

module Automata.MyhillNerode where

open import Automata.Imports
open import Automata.EQRelation
open import Automata.DFA
open import Cubical.HITs.PropositionalTruncation as trunc
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Foundations.Equiv
open import Cubical.Data.SumFin


record MNRel (Sf : FinSet ℓ-zero) (L : List (Sf .fst) → Bool) : Type₁ where
    constructor MNR
    S : Type
    S = Sf .fst

    field
        R : Relation (List S)
        EQR : is-EQ R
        extend-invar : ∀ {x y} → R x y → ∀ a → R (a ∷ x) (a ∷ y)
        L-respect : ∀ {x y} → R x y → L x ≡ L y
        fin-index : isFinSet ((List S) // (R , EQR))

func-set : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
           → isSet B → isSet (A → B)
func-set setB f g p q i = funExt (λ x → setB _ _ (cong (λ h → h x) p) (cong (λ h → h x) q) i)

cDFA-to-MNR : {Sf : FinSet ℓ-zero} → ((M , _) : connected-DFA Sf) → MNRel Sf (DFA.L M)
cDFA-to-MNR {Sf@(S , _)} (M@(dfa Q Q-fin d start final), connect) = MNR
    R R-EQ (λ Rxy a → cong (λ q → d q a) Rxy) (λ Rxy → cong final Rxy)
    (Q-size , trunc.rec squash₁ (∣_∣₁ ∘ translate) (Q-fin .snd))
    where
        R : Relation (List S)
        R x y = DFA.dh M start x ≡ DFA.dh M start y

        R-EQ : is-EQ R
        R-EQ = EQ refl sym _∙_

        Q-size : ℕ
        Q-size = Q-fin .fst

        translate : Q ≃ Fin Q-size → (List S // (R , R-EQ)) ≃ Fin Q-size
        translate e = f , fEquiv where

            Q≅Fin : Iso Q (Fin Q-size)
            Q≅Fin = equivToIso e

            fun : Q → Fin Q-size
            fun = Iso.fun Q≅Fin

            inv : Fin Q-size → Q
            inv = Iso.inv Q≅Fin

            f : List S // (R , R-EQ) → Fin Q-size
            f (class x) = fun (DFA.dh M start x)
            f (eq/ x y Rxy i) = fun (Rxy i)
            f (squash/ x y p q i j) = isSetFin (f x) (f y) (cong f p) (cong f q) i j

            fEquiv : isEquiv f
            fEquiv .equiv-proof n = trunc.rec isPropIsContr proof (connect (inv n)) where

                proof : Σ[ x ∈ List S ] DFA.dh M start x ≡ inv n → (isContr (fiber f n))
                proof (x , px) = ((class x) , cong fun px ∙ Iso.sec Q≅Fin n) , contract where
                    contract : ∀ x' → (class x , cong fun px ∙ Iso.sec Q≅Fin n) ≡ x'
                    contract (x/ , fx/=n) = ΣPathP
                        (elimProp {P = λ y/ → (f y/ ≡ n → class x ≡ y/)}
                            (λ _ → isPropΠ λ _ → squash/ _ _) class-pf x/ fx/=n ,
                        (isProp→PathP (λ _ → isSetFin _ _) _ _)) where
                            class-pf : ∀ y → f (class y) ≡ n → class x ≡ class y
                            class-pf y py = eq/ x y
                                (px ∙ cong inv (sym py) ∙ Iso.ret Q≅Fin _)


MNR-to-cDFA : {Sf : FinSet ℓ-zero} (L : List (Sf .fst) → Bool) →
             MNRel Sf L → Σ[ (M , _) ∈ (connected-DFA Sf) ] DFA.L M ≡ L
MNR-to-cDFA {Sf@(S , _)} L (MNR R EQR extend-invar L-respect fin-index) =
    (M , connect) , funExt (cong within-L ∘ dh-lem) where

    delta : List S // (R , EQR) → S → List S // (R , EQR)
    delta = Automata.EQRelation.rec (func-set squash/) (λ x a → class (a ∷ x))
            (λ x y Rxy → funExt (λ a → eq/ _ _ (extend-invar Rxy a)))

    within-L : List S // (R , EQR) → Bool
    within-L = Automata.EQRelation.rec isSetBool L (λ _ _ → L-respect)

    M : DFA Sf
    M = dfa (List S // (R , EQR)) fin-index delta (class []) within-L

    dh-lem : (x : List S) → DFA.dh M (class []) x ≡ class x
    dh-lem [] = refl
    dh-lem (a ∷ x) = cong (λ y → DFA.d M y a) (dh-lem x)

    connect : ∀ x/ → ∃[ y ∈ List S ] DFA.dh M (class []) y ≡ x/
    connect x/ = subst (λ f → ∃[ z ∈ List S ] (f z ≡ x/)) (sym (funExt dh-lem)) ([]surjective x/)

