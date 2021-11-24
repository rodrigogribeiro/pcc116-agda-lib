{-# OPTIONS --without-K #-}

module HTT.Basics.Sum where

open import HTT.Basics.Universes
open import HTT.Basics.Empty

data _+_ {U V}(A : Type U)(B : Type V) : Type (U ⊔ V) where
  inl : A → A + B
  inr : B → A + B

isDec : ∀ {U}(A : Type U) → Type U
isDec A = A + (¬ A)

+-elim : ∀ {U V W}{A : Type U}{B : Type V}{C : Type W} →
           A + B → (A → C) → (B → C) → C
+-elim (inl x) f _ = f x
+-elim (inr x) _ g = g x
