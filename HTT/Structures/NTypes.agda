module HTT.Structures.NTypes where

open import HTT.Structures.HProp
open import HTT.Structures.HSet
open import HTT.Basics.BasicTypes
open import HTT.Structures.Contractible


-- definition of n types

hasLevel : ∀ {U} → ℕ → Type U → Type U
hasLevel zero    A = isContr A
hasLevel (suc n) A = (x y : A) → hasLevel n (x ≡ y)

-- Propositions are 1-types

isProp-is1Type : ∀ {U}{A : Type U} → isProp A → hasLevel 1 A
isProp-is1Type p x y = ((! (p x x)) ∙ p x y)
                       , (λ { refl → ∙-cancel-right (p x x)})

-- cumulativeness Σ-≡

hasLevel-cumulative : ∀ {U}{n : ℕ}{A : Type U} →
                        hasLevel n A →
                        hasLevel (suc n) A
hasLevel-cumulative {n = zero} (a , p) x y = ((! p x) ∙ p y) , λ {refl → ∙-cancel-right (p x)}
hasLevel-cumulative {n = suc n} L x y = hasLevel-cumulative (L x y)

isContr-isProp : ∀ {U}{A : Type U} → isProp (isContr A)
isContr-isProp {A = A} (x , p) (y , q) = Σ-≡ (p y) (extensionality (λ z → fst (A-isSet y z _ (q z))))
  where
    A-isSet : hasLevel 2 A
    A-isSet = hasLevel-cumulative (hasLevel-cumulative (x , p))

hasLevel-isProp : ∀ {U}{A : Type U}(n : ℕ) → isProp (hasLevel n A)
hasLevel-isProp zero        = isContr-isProp
hasLevel-isProp (suc n) f g
  = extensionality2 (λ x y → hasLevel-isProp n (f x y) (g x y))
