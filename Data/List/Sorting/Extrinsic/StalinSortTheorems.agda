open import Algebra.Order.Order
open import Basics.Admit
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties

module Data.List.Sorting.Extrinsic.StalinSortTheorems {A : Set}
                                                      {_<_ : Relation A}
                                                      (M : IsTotalOrder _<_) where

open IsTotalOrder M public
open import Data.List.Sorting.Extrinsic.StalinSort M
open import Data.List.Relation.Sorted M
open import Data.List.Relation.Sublist

stalinSort-sorted : (xs : List A) → Sorted (stalinSort xs)
stalinSort-sorted = admit

stalinSort-sublist : (xs : List A) → (stalinSort xs) ⊆ xs
stalinSort-sublist = admit
