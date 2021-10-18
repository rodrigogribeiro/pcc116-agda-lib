open import Algebra.Order.Order
open import Basics.Admit
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties

module Data.List.Sorting.Intrinsic.InsertionSort {A : Set}
                                                 {_<_ : Relation A}
                                                 (M : IsTotalOrder _<_) where

open import  Data.List.Sorting.Intrinsic.Sorting M

insert : ∀ {xs}(x : A) → Sorting xs → Sorting (x ∷ xs)
insert = admit

isort : (xs : List A) → Sorting xs
isort = admit
