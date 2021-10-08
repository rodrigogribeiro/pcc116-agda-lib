module Algebra.Order.Order where

  open import Relation.Properties

  record IsPartialOrder {A : Set}(_≤_ : Relation A) : Set where
    field
      reflexive      : Reflexive _≤_
      anti-symmetric : AntiSymmetric _≤_
      transitive     : Transitive _≤_

  record IsTotalOrder {A : Set}(_≤_ : Relation A) : Set where
    field
      partial : IsPartialOrder _≤_
      total   : Total _≤_
