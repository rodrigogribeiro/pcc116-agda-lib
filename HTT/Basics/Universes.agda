{-# OPTIONS --without-K #-}

module HTT.Basics.Universes where

open import Agda.Primitive
 renaming (
            Level to Universe
          ; lzero to U₀
          ; lsuc  to _⁺
          ; Setω  to Uω
          )
 using    (_⊔_) public

Type = λ ℓ → Set ℓ

case_of_ : ∀ {U V}{A : Type U}{B : Type V} → A → (A → B) → B
case x of f =  f x

id : ∀ {U}{A : Type U} → A → A
id x = x

_∘_ : ∀ {U V W}{A : Type U}{B : Type V}{C : Type W} →
        (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

record Lift {U} V (A : Type U) : Type (U ⊔ V) where
  constructor lift
  field lower : A

open Lift public
