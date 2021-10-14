module Data.Vec.Matrix where

open import Basics.Admit

open import Data.Nat.Nat
open import Data.Vec.Vec

-- matrices

Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
Matrix A n m = Vec (Vec A n) m

-- matrix transposition

transpose : ∀ {a}{A : Set a}{n m} → Matrix A n m → Matrix A m n
transpose = admit

-- identity matrix

idMatrix : ∀ {n} → Matrix ℕ n n
idMatrix = admit

-- all zero matrix

zeroMatrix : ∀ {n m} → Matrix ℕ n m
zeroMatrix = admit

-- matrix addition

_+M_ : ∀ {n m} → Matrix ℕ n m → Matrix ℕ n m → Matrix ℕ n m
_+M_ = admit

-- matrix multiplication

_*M_ : ∀ {n p m} → Matrix ℕ n p → Matrix ℕ p m → Matrix ℕ n m
_*M_ = admit
