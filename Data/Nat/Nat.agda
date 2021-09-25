module Data.Nat.Nat where

open import Data.Bool.Bool

-- basic definitions for natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- natural number addition

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

-- natural number subtraction

infixl 6 _-_

_-_ : ℕ → ℕ → ℕ
n     - zero  = n
zero  - suc m = zero
suc n - suc m = n - m


-- natural number multiplication

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m

-- exponentiation

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

-- comparison

_≡B_ : ℕ → ℕ → Bool
zero ≡B zero = true
zero ≡B suc m = false
suc n ≡B zero = false
suc n ≡B suc m = n ≡B m
