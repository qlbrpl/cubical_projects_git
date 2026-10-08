module hcompExperiments where

open import Cubical.Foundations.Prelude public

private
    variable
        ℓ : Level
        A : Type ℓ
        w x y z : A

d : I → I
d i = i ∨ ~ i

∙filler₂ : (p : x ≡ y) (q : y ≡ z) → Square p refl (p ∙ q) q
∙filler₂ p q i j = hcomp shape₂ (p (i ∨ j)) where
    shape₂ : I → Partial (d i ∨ j) _
    shape₂ k (j = i1) = q (i ∧ k)
    shape₂ k (i = i0) = p j
    shape₂ k (i = i1) = q k

r=rr : ∀ {ℓ} {A : Type ℓ} {a : A} → refl {x = a} ≡ refl ∙ refl
r=rr = compPath-filler refl refl

r=rr' : ∀ {ℓ} {A : Type ℓ} {a : A} → refl {x = a} ≡ refl ∙ refl
r=rr' {a = a} i j = hcomp s a where
    s : I → Partial (d i ∨ d j) _
    s k (i = i0) = a
    s k (i = i1) = (refl {x = a} ∙ refl) (j ∨ ~ j ∨ ~ k)
    s k (j = i0) = a
    s k (j = i1) = a

test : ∀ {ℓ} {A : Type ℓ} {a : A} {j : I} →
       hcomp (doubleComp-faces (λ _ → a) (λ _ → a) (j      )) a ≡
       hcomp (doubleComp-faces (λ _ → a) (λ _ → a) (j ∨ ~ j)) a
test = refl

∙filler₂' : (p : x ≡ y) (q : y ≡ z) → Square p refl (p ∙ q) q
∙filler₂' {x = x} p q = J (λ z' q' → Square p refl (p ∙ q') q') (J (λ y' p' → Square p' refl (p' ∙ refl) refl)
        (subst (λ c → Square refl refl c refl) r=rr refl) p) q

square→commutes : {p : w ≡ x} {q : y ≡ z} {r : w ≡ y} {s : x ≡ z} →
                  Square p q r s → p ∙ s ≡ r ∙ q
square→commutes {p = p} {q} {r} {s} fill i j = hcomp shape (fill i j) where
    shape : I → Partial (d i ∨ d j) _
    shape k (i = i0) = compPath-filler p s k j
    shape k (i = i1) = ∙filler₂' r q j (~ k)
    shape k (j = i0) = r (i ∧ ~ k)
    shape k (j = i1) = s (i ∨ k)

a : ?
a = Square≡doubleCompPath
