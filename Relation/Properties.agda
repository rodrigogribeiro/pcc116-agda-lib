module Relation.Properties where

  open import Data.Sum.Sum

  open import Relation.Equality.Propositional

  Relation : Set → Set₁
  Relation A = A → A → Set

  Reflexive : ∀ {A} → Relation A → Set
  Reflexive {A} _≤_ = ∀ {x} → x ≤ x

  AntiSymmetric : ∀ {A} → Relation A → Set
  AntiSymmetric {A} _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

  Transitive : ∀ {A} → Relation A → Set
  Transitive {A} _≤_ = ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

  Total : ∀ {A} → Relation A → Set
  Total {A} _≤_ = ∀ x y → x ≤ y ⊎ y ≤ x
