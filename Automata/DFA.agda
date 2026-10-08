{-# OPTIONS --safe #-}

module Automata.DFA where

open import Automata.Imports
open import Automata.EQRelation
open import Cubical.Foundations.Transport
open import Cubical.HITs.PropositionalTruncation



record DFA (Sf : FinSet ℓ-zero) : Type₁ where
    constructor dfa

    S : Type
    S = Sf .fst

    field
        Q : Type
        Q-fin : isFinSet Q
        d : Q → S → Q
        start : Q
        final : Q → Bool

    dh : Q → List S → Q
    dh q [] = q
    dh q (x ∷ xs) = d (dh q xs) x

    L : List S → Bool
    L xs = final (dh start xs)

    setS : isSet S
    setS = isFinSet→isSet (Sf .snd)

record IsoDFA (Sf : FinSet ℓ-zero) (M1 : DFA Sf) (M2 : DFA Sf) : Type where
    constructor iso-dfa
    field
        Q1≅Q2 : Iso (DFA.Q M1) (DFA.Q M2)
        homo : ∀ q a → (Iso.fun Q1≅Q2 (DFA.d M1 q a)) ≡ DFA.d M2 (Iso.fun Q1≅Q2 q) a
        start-match : Iso.fun Q1≅Q2 (DFA.start M1) ≡ DFA.start M2
        final-match : ∀ q → DFA.final M1 q ≡ DFA.final M2 (Iso.fun Q1≅Q2 q)

    homo-ext : ∀ q x → (Iso.fun Q1≅Q2 (DFA.dh M1 q x)) ≡ DFA.dh M2 (Iso.fun Q1≅Q2 q) x
    homo-ext q [] = refl
    homo-ext q (a ∷ x) = homo (DFA.dh M1 q x) a ∙ cong (λ q → DFA.d M2 q a) (homo-ext q x)

    same-lang : DFA.L M1 ≡ DFA.L M2
    same-lang = funExt λ x →
        final-match (DFA.dh M1 (DFA.start M1) x) ∙
        cong (DFA.final M2) (homo-ext (DFA.start M1) x ∙
        cong (λ q → DFA.dh M2 q x ) start-match)

DFAΣ : (Sf : FinSet ℓ-zero) → Type₁
DFAΣ (S , _) = Σ[ Q ∈ Type ] isFinSet Q × (Q → S → Q) × Q × (Q → Bool)

DFA≅DFAΣ : (Sf : FinSet ℓ-zero) → Iso (DFA Sf) (DFAΣ Sf)
DFA≅DFAΣ Sf = iso fun inv (λ _ → refl) (λ _ → refl) where
    fun : DFA Sf → DFAΣ Sf
    fun (dfa Q fin-state d start final) = Q , fin-state , d , start , final
    inv : DFAΣ Sf → DFA Sf
    inv (Q , fin-state , d , start , final) = dfa Q fin-state d start final

DFA≡ : {Sf : FinSet ℓ-zero} (M1 : DFA Sf) → (M2 : DFA Sf) →
        IsoDFA Sf M1 M2 → M1 ≡ M2
DFA≡ M1@(dfa Q1 Q1-fin d1 s1 F1)
                 M2@(dfa Q2 Q2-fin d2 s2 F2)
                (iso-dfa Q1≅Q2 homo s-match F-match) =
    sym (Iso.ret (DFA≅DFAΣ _) M1) ∙
    cong (Iso.inv (DFA≅DFAΣ _)) DFAΣ≡ ∙
    Iso.ret (DFA≅DFAΣ _) M2 where

        DFAΣ≡ : (Q1 , Q1-fin , d1 , s1 , F1) ≡ (Q2 , Q2-fin , d2 , s2 , F2)
        DFAΣ≡ = ΣPathP
            (isoToPath Q1≅Q2 , ΣPathP
            (isProp→PathP (λ _ → isPropIsFinSet) _ _ , ΣPathP
            (toPathP (funExt (funExt ∘ dpath)) , ΣPathP
            (toPathP (transportRefl _ ∙ s-match) ,
             toPathP (funExt (λ q → cong (λ p → F1 (Iso.inv Q1≅Q2 p)) (transportRefl q) ∙
                              F-match (Iso.inv Q1≅Q2 q) ∙
                              cong F2 (Iso.sec Q1≅Q2 q))))))) where
                dpath = λ q a → (transportRefl _ ∙
                    cong₂ (λ p b → Iso.fun Q1≅Q2 (d1 (Iso.inv Q1≅Q2 p) b))
                        (transportRefl _)
                        (transportRefl _))
                    ∙ homo (Iso.inv Q1≅Q2 q) a ∙ cong (λ p → d2 p a) (Iso.sec Q1≅Q2 q)

DFA-≡toIso : {Sf : FinSet ℓ-zero}
             (M1 : DFA Sf) → (M2 : DFA Sf) →
             M1 ≡ M2 → IsoDFA Sf M1 M2
DFA-≡toIso {(S , _)}
        M1@(dfa Q1 Q1-fin d1 s1 F1) M2@(dfa Q2 Q2-fin d2 s2 F2)
        M1≡M2 = iso-dfa (pathToIso Q1≡Q2) homo (fromPathP s1≡s2) F-match where
            ΣM1≡ΣM2 : Iso.fun (DFA≅DFAΣ _) M1 ≡ Iso.fun (DFA≅DFAΣ _) M2
            ΣM1≡ΣM2 = cong (Iso.fun (DFA≅DFAΣ _)) M1≡M2

            Q1≡Q2 : Q1 ≡ Q2
            Q1≡Q2 = PathPΣ ΣM1≡ΣM2 .fst

            f : Q1 → Q2
            f = transport Q1≡Q2

            d1≡d2 : PathP (λ z → Q1≡Q2 z → S → Q1≡Q2 z) d1 d2
            d1≡d2 = PathPΣ (PathPΣ (PathPΣ ΣM1≡ΣM2 .snd) .snd) .fst

            homo : (q : Q1) (a : S) → f (d1 q a) ≡ d2 (f q) a
            homo q a = sym (cong (transp (λ i → Q1≡Q2 i) i0)
                       (cong₂ d1 (transport⁻Transport Q1≡Q2 q) (transportRefl _))) ∙
                       funExt⁻ (funExt⁻ (fromPathP d1≡d2) (f q)) a

            s1≡s2 : PathP (λ z → Q1≡Q2 z) s1 s2
            s1≡s2 = PathPΣ (PathPΣ (PathPΣ (PathPΣ ΣM1≡ΣM2 .snd) .snd) .snd) .fst

            F1≡F2 : PathP (λ i → Q1≡Q2 i → Bool) F1 F2
            F1≡F2 = PathPΣ (PathPΣ (PathPΣ (PathPΣ ΣM1≡ΣM2 .snd) .snd) .snd) .snd

            F-match : (q : Q1) → F1 q ≡ F2 (transport Q1≡Q2 q)
            F-match q = funExt⁻ (sym (fromPathP (symP F1≡F2))) q

Iso-EQR : (Sf : FinSet ℓ-zero) → is-EQ (IsoDFA Sf)
Iso-EQR Sf = path-EQ (IsoDFA Sf) DFA≡ DFA-≡toIso


connected-DFA : (Sf : FinSet ℓ-zero) → Type₁
connected-DFA Sf@(S , _) = Σ[ M ∈ (DFA Sf) ] (∀ q → ∃[ x ∈ List S ] DFA.dh M (DFA.start M) x ≡ q)

connected-DFA-for-lang : ((S , S-fin) : FinSet ℓ-zero) → (L : List S → Bool) → Type₁
connected-DFA-for-lang Sf L = Σ[ (M , _) ∈ connected-DFA Sf ] DFA.L M ≡ L


cDFA≡ : {Sf : FinSet ℓ-zero} (M1 M2 : connected-DFA Sf) →
        IsoDFA Sf (M1 .fst) (M2 .fst) → M1 ≡ M2
cDFA≡ (M1 , conn1) (M2 , conn2) iso12 = ΣPathP
    ((DFA≡ M1 M2 iso12) , (isProp→PathP (λ _ → isPropΠ λ _ → squash₁) _ _))
