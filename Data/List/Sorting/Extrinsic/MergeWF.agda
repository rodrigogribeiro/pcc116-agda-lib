module Data.List.Sorting.Extrinsic.MergeWF (A : Set) where

open import Data.List.List
open import Data.List.Sorting.Extrinsic.LengthWF A
open import Data.Product.Product
open import Relation.Induction.Lexicographic _<<_ _<<_
open import Relation.Induction.WellFounded
open import Relation.Properties

merge-wf : WellFounded _⊏_
merge-wf = wellFounded length-wf length-wf

_<*_ : Relation (List A × List A)
x <* y = x ⊏ y
