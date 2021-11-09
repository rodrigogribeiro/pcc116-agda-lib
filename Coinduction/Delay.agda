{-# OPTIONS --sized-types #-}

module Coinduction.Delay where

open import Algebra.Monad.Monad
open import Coinduction.Size
open import Data.Function.Function


data Delay' (i : Size) (A : Set) : Set


record Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay' j A

data Delay' i A where
  return' : A         → Delay' i A
  later'  : Delay i A → Delay' i A

open Delay public

private
  returnDelay : ∀{A i} → A → Delay i A
  returnDelay a .force = return' a

  bindDelay : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
  bindDelay m k .force = case m .force of λ where
    (return' a) → k a .force
    (later' m') → later' (bindDelay m' k)

instance
  monadDelay : ∀ {i} → Monad (Delay i)
  return {{monadDelay}} = returnDelay
  _>>=_ {{monadDelay}} = bindDelay
