module Algebra.Monoid.Monoid where

open import Basics.Admit

open import Data.Nat.Nat
open import Data.Nat.NatTheorems

open import Relation.Equality.Propositional

record IsMonoid {a}{A : Set a}(_⊕_ : A → A → A)(e : A) : Set a where
  field
    assoc : ∀ {x y z : A} → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    identityˡ : ∀ {x} → e ⊕ x ≡ x
    identifyʳ : ∀ {x} → x ⊕ e ≡ x

-- sum and zero forms a monoid

+-Monoid : IsMonoid _+_ 0
+-Monoid
  = record { assoc = λ {x}{y}{z} → +-assoc x y z
           ; identityˡ = refl
           ; identifyʳ = λ {x} → +-zero-right x }

-- multiplication and one forms a monoid

*-Monoid : IsMonoid _*_ 1
*-Monoid = admit
