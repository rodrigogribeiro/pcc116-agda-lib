open import Algebra.Order.Order
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties


module Data.List.Sorting.Intrinsic.Sorting {A : Set}
                                           {_<_ : Relation A}
                                           (M : IsTotalOrder _<_) where


open IsTotalOrder M public
open import Data.List.Relation.Permutation public
open import Data.List.Relation.Sorted M public



-- definition of a type for sorting algorithms

record Sorting (input : List A) : Set where
  field
    output   : List A
    isSorted : Sorted output
    isPerm   : input ≈ output

open Sorting public
