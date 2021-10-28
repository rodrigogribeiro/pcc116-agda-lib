module Data.Nat.Div.DivIntrinsic where

open import Basics.Admit

open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma
open import Relation.Induction.Natural
open import Relation.Equality.Propositional

Division : ℕ → Set
Division m = ∀ (n : ℕ) → 0 < n → Σ ℕ (λ q → Σ ℕ (λ r → m ≡ q * n + r × r < n))

-- prove o algoritmo de divisão usando fuel, well founded recursion e Bove Capretta predicates.

module DivisionFuel where

  divFuel : ∀ (m : ℕ)(fuel : ℕ) → Division m
  divFuel = admit

module DivisionWF where

  divWF : ∀ (m : ℕ) → Division m
  divWF = admit

module DivisionBove where

  divBove : ∀ (m : ℕ) → Division m
  divBove = admit
