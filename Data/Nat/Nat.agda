module Data.Nat.Nat where

import Equality.Propositional

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

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m
