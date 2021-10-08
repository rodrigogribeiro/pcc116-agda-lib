module Data.Biconditional.Biconditional where

open import Basics.Level

-- biconditional

infix 3 _⇔_

record _⇔_ {l₁ l₂}(A : Set l₁)
                  (B : Set l₂) : Set (l₁ ⊔ l₂) where
  field
    to : A → B
    from : B → A
