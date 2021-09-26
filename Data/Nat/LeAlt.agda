module Data.Nat.LeAlt where

open import Basics.Admit

open import Basics.Level

open import Data.Bool.Bool
open import Data.Nat.Nat
open import Data.Nat.Le hiding (Total)
open import Data.Nat.NatTheorems

open import Relation.Equality.Propositional


-- alternative definition of the ≤ relation

infix 4 _≤'_

data _≤'_ : ℕ → ℕ → Set where
  ≤'-refl : ∀ {n} → n ≤' n
  ≤'-step : ∀ {n m} → n ≤' m
              → n ≤' (suc m)


-- Exercise 4. Prove that ≤' is a ordering relation

≤'-trans : ∀ {n m p} → n ≤' m
                     → m ≤' p
                     → n ≤' p
≤'-trans = admit

≤'-antisym : ∀ {x y} → x ≤' y →
                       y ≤' x →
                       x ≡ y
≤'-antisym = admit


-- Exercise 5. Prove that ≤' is total

data Total : ℕ → ℕ → Set where
  forward : ∀ {n m} →
              n ≤' m →
              Total n m
  flipped : ∀ {n m} →
              m ≤' n →
              Total n m


≤'-total : ∀ (n m : ℕ) → Total n m
≤'-total = admit

-- Exercise 6. Prove basic facts about ordering 

≤'-+-left : ∀ {n m p} → n ≤' m → n ≤' p + m
≤'-+-left = admit

-- monotonicity of addition

-- Exercise 7.

+-mono-≤' : ∀ {n m p q} → n ≤' m → p ≤' q → (n + p) ≤' (m + q)
+-mono-≤' = admit

-- Exercise 8. Prove the equivalence between ≤ definitions

≤⇒≤' : ∀ {n m} → n ≤ m → n ≤' m
≤⇒≤' = admit

≤'⇒≤ : ∀ {n m} → n ≤' m → n ≤ m
≤'⇒≤ = admit
