open import Algebra.Order.Order
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties

module Data.List.Sorting.Extrinsic.InsertionSort {A : Set}
                                                 {_<_ : Relation A}
                                                 (M : IsTotalOrder _<_) where

open IsTotalOrder M public

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys) with total x y
...| inj₁ x≤y = x ∷ y ∷ ys
...| inj₂ ¬x≤y = y ∷ insert x ys

isort : List A → List A
isort []       = []
isort (x ∷ xs) = insert x (isort xs)
