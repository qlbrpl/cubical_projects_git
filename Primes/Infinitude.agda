{-# OPTIONS --safe #-}

module Primes.Infinitude where

open import Primes.Imports
open import Primes.Lemmas
open import Primes.Base
open import Primes.Split
open import Primes.Concrete
open import Primes.Factors
open import Primes.DecProps hiding (Some)


nextPrime : (n : ℕ) → Σ[ p ∈ ℕ ] ((n < p) × (isPrime p)) × ((z : ℕ) → (n < z) × isPrime z → p ≤ z)
nextPrime n = findLeast (((newPrime n) .snd)) (DecProd (<Dec n) DecPrime)

nthPrime : (n : ℕ) → Σ[ p ∈ ℕ ] isPrime p × (countBelow isPrime DecPrime p ≡ n)
nthPrime zero = (least-prime .fst , least-prime .snd .fst , refl) where
    least-prime = findLeast prime2 DecPrime
nthPrime (suc n) = (next-prime .fst , next-prime .snd .fst .snd , snprimes) where
    IH = nthPrime n

    p#n = IH .fst
    p#n-prime = IH .snd .fst
    #p<p#n=n = IH .snd .snd

    next-prime : Σ[ q ∈ ℕ ] ((p#n < q) × isPrime q) × (∀ z → (p#n < z) × isPrime z → q ≤ z)
    next-prime = nextPrime p#n

    q = next-prime .fst
    p#n<q = next-prime .snd .fst .fst
    p#n≤q = <-weaken p#n<q
    q-prime = next-prime .snd .fst .snd
    q-least = next-prime .snd .snd

    sum : countBelow isPrime DecPrime q
          ≡ countRange isPrime DecPrime p#n q p#n≤q + countBelow isPrime DecPrime p#n
    sum = sym (countWorks isPrime DecPrime p#n q p#n≤q)
    p1 : countRange isPrime DecPrime p#n q p#n≤q ≡ 1
    p1 = leastAboveLow isPrime DecPrime p#n q p#n-prime
         (isPropDec (primeProp p#n) (DecPrime p#n) (yes p#n-prime))
         q-least p#n<q

    snprimes : countBelow isPrime DecPrime q ≡ suc n
    snprimes = sum ∙ add-equations p1 #p<p#n=n


open Iso renaming (ret to leftInv ; sec to rightInv)
ℕ≅primeℕ : Iso ℕ (Σ ℕ isPrime)
fun      ℕ≅primeℕ n = (pn .fst , pn .snd .fst) where pn = nthPrime n
inv      ℕ≅primeℕ (p , _) = countBelow isPrime DecPrime p
leftInv  ℕ≅primeℕ n = nthPrime n .snd .snd
rightInv ℕ≅primeℕ (p , p-prime) =
    ΣPathP (answer , isProp→PathP (λ i → primeProp (answer i)) pn-prime p-prime) where
        pn = nthPrime (countBelow isPrime DecPrime p)
        pn-prime = pn .snd .fst
        answer : pn .fst ≡ p
        answer = countBelowYesInj isPrime DecPrime (pn .fst) p pn-prime p-prime
                 (isPropDec (primeProp (pn .fst)) (DecPrime (pn .fst)) (yes pn-prime))
                 (isPropDec (primeProp p) (DecPrime p) (yes p-prime))
                 (pn .snd .snd)


open import MyhillCB.MyhillIso
open import MyhillCB.Base
open import Cubical.Data.Empty as ⊥

nthPrime-nopf : ℕ → Σ ℕ isPrime
nthPrime-nopf n = p#n .fst , p#n .snd .fst where p#n = nthPrime n

nthPrime-nopf-inj : isInjective nthPrime-nopf
nthPrime-nopf-inj {m} {n} pm=pn = sym p1 ∙ cong (countBelow isPrime DecPrime) (fst (PathPΣ pm=pn)) ∙ p2 where
    p1 : countBelow isPrime DecPrime (nthPrime m .fst) ≡ m
    p1 = nthPrime m .snd .snd
    p2 : countBelow isPrime DecPrime (nthPrime n .fst) ≡ n
    p2 = nthPrime n .snd .snd

CBIso : Iso ℕ (Σ ℕ isPrime)
CBIso = CantorBernstein-ret
    ((λ n → n) , (Some , (λ _ → refl)))
    (fst , (optP , ret))
    nthPrime-nopf-inj fstInj where
        optP : ℕ → Opt (Σ ℕ isPrime)
        optP n with DecPrime n
        ... | yes pn = Some (n , pn)
        ... | no _ = None

        ret : (x : Σ ℕ isPrime) → optP (fst x) ≡ Some x
        ret (n , np) with DecPrime n
        ... | no ¬np = ⊥.rec (¬np np)
        ... | yes np' = cong Some (ΣPathP (refl , (primeProp _ _ _)))

        fstInj : isInjective fst
        fstInj {_ , xp} {_ , yp} gm=gn = ΣPathP (gm=gn , (isProp→PathP (λ _ → primeProp _) xp yp))
