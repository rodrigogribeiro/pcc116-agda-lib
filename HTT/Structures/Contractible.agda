{-# OPTIONS --without-K #-}
module HTT.Structures.Contractible where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HProp


-- definition of contractible types

isContr : ∀ {U} → Type U → Type U
isContr A = Σ {A = A} (λ x → (y : A) → x ≡ y)


-- unit is contractible

⊤-isContr : isContr ⊤
⊤-isContr = ⋆ , (λ { ⋆ → refl})

-- singletons are contractible

Singleton : ∀ {U}{A : Type U} → A → Type U
Singleton {A = A} x = Σ {A = A} (λ y → x ≡ y)

Singleton-isContr : ∀ {U}{A : Type U}(x : A) → isContr (Singleton x)
Singleton-isContr x = (x , refl) , (λ {(y , refl) → refl})

-- contractible types are propositions

Contr-isProp : ∀ {U}{A : Type U} → isContr A → isProp A
Contr-isProp (x , p) y z with p y | p z
...| refl | refl = refl
