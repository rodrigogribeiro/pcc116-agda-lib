{-# OPTIONS --without-K #-}

module HTT.Basics.Unit where

open import HTT.Basics.Universes

-- unit type

data ⊤ : Type U₀ where
  ⋆ : ⊤
