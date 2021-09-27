module Data.Nat.EvenOdd where

open import Basics.Admit

open import Data.Nat.Nat

open import Relation.Equality.Propositional

-- definition of even

data Even : ℕ → Set where
  zero : Even 0
  suc  : ∀ {n} → Even n
               → Even (2 + n)


data Odd : ℕ → Set where
  one : Odd 1
  suc : ∀ {n} → Odd n
              → Odd (2 + n)


-- Exercises

2*-even : ∀ {n} → Even (2 * n)
2*-even = admit

+-even-even : ∀ {n m} → Even n → Even n → Even (n + m)
+-even-even = admit

+-even-odd : ∀ {n m} → Even n → Odd m → Odd (n + m)
+-even-odd = admit

+-odd-odd : ∀ {n m} → Odd n → Odd m → Even (n + m)
+-odd-odd = admit
