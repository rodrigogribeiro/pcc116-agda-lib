{-# OPTIONS --without-K #-}

module HTT.Basics.Bool where

open import HTT.Basics.Universes

data Bool : Type U₀ where
  true false : Bool

not : Bool → Bool
not false = true
not true = false
