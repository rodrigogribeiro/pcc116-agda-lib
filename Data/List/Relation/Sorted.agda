open import Algebra.Order.Order

open import Data.List.List

open import Relation.Properties

module Data.List.Relation.Sorted {A : Set}
                                 {_<_ : Relation A}
                                 (M : IsTotalOrder _<_) where

open IsTotalOrder M public


data Sorted : List A → Set where
  empty : Sorted []
  single : ∀ {x} → Sorted [ x ]
  many : ∀ {y x xs} → y < x
                    → Sorted (x ∷ xs)
                    → Sorted (y ∷ x ∷ xs)
