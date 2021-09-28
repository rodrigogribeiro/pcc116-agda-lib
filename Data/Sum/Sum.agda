module Data.Sum.Sum where

open import Basics.Level

-- definition of the sum type

infix 1 _⊎_

data _⊎_ {l₁ l₂}(A : Set l₁)
                (B : Set l₂) : Set (l₁ ⊔ l₂) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B


-- elimination of ⊎

⊎-elim : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
           (A → C) → (B → C) → A ⊎ B → C
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y

