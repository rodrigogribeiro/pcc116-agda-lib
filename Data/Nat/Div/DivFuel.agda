module Data.Nat.Div.DivFuel where

open import Data.Empty.Empty
open import Data.Nat.Nat
open import Data.Nat.Div.NonZero
open import Data.Maybe.Maybe
open import Data.Unit.Unit


Fuel : Set
Fuel = ℕ

div-fuel : Fuel → (n m : ℕ).{{_ : NonZero m}} → Maybe ℕ
div-fuel zero n m = nothing
div-fuel (suc gas) 0 m = just 0
div-fuel (suc gas) n m
  = map suc (div-fuel gas (n - m) m)

div : (n m : ℕ).{{_ : NonZero m}} → Maybe ℕ
div n m = div-fuel n n m
