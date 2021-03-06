{-# OPTIONS --without-K #-}

module HTT.Basics.Bool where

open import HTT.Basics.Universes

data Bool : Type Uā where
  true false : Bool

not : Bool ā Bool
not false = true
not true = false
