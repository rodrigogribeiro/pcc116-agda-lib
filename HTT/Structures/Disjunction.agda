{-# OPTIONS --without-K #-}
module HTT.Structures.Disjunction where

open import HTT.Basics.BasicTypes
open import HTT.Structures.Truncation

_∨_ : ∀ {U V} → Type U → Type V → Type (U ⊔ V)
A ∨ B = ∥ A + B ∥

in-left : ∀ {U V}{A : Type U}{B : Type V} → A → A ∨ B
in-left x = ∣ inl x ∣

in-right : ∀ {U V}{A : Type U}{B : Type V} → B → A ∨ B
in-right x = ∣ inr x ∣
