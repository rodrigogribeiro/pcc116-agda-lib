{-# OPTIONS --without-K #-}
module HTT.Structures.Existential where

open import HTT.Basics.BasicTypes
open import HTT.Structures.Truncation

∃ : ∀ {U V}(A : Type U)(B : A → Type V) → Type (U ⊔ V)
∃ A B = ∥ Σ {A = A} B ∥
