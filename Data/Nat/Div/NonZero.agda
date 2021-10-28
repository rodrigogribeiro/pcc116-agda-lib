module Data.Nat.Div.NonZero where

open import Data.Empty.Empty
open import Data.Nat.Nat
open import Data.Unit.Unit

NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤
