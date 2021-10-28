module Data.Nat.Div.DivBoveCapretta where

open import Data.Nat.Nat
open import Data.Nat.Div.NonZero

data _≺_ : ℕ → ℕ → Set where
  ≺-base : ∀ {m} → 0 ≺ suc m
  ≺-one  : ∀ {n} → (suc n) ≺ 1
  ≺-step : ∀ {n m} → (n - m) ≺ m →
                      n ≺ (suc m)

≺-all : ∀ (n m : ℕ).{{_ : NonZero m}} → n ≺ m
≺-all zero (suc m)          = ≺-base
≺-all (suc n) (suc zero)    = ≺-one
≺-all (suc n) (suc (suc m)) = ≺-step (≺-all (n - m) (suc m))

div-≺ : ∀ {n m : ℕ} → n ≺ m → ℕ
div-≺ ≺-base       = 0
div-≺ {n} ≺-one    = n
div-≺ (≺-step n≺m) = suc (div-≺ n≺m)

div : ∀ (n m : ℕ).{{_ : NonZero m}} → ℕ
div n m = div-≺ (≺-all n m)
