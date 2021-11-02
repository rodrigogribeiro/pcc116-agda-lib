{-# OPTIONS --sized-types #-}

module Everything where

-- Importing every module from the library

open import Algebra.Monoid.Monoid
open import Algebra.Order.Order

open import Basics.Admit
open import Basics.Level

open import Coinduction.Size
open import Coinduction.DelayMonad

open import Data.Biconditional.Biconditional
open import Data.Biconditional.BiconditionalTheorems
open import Data.Bool.Bool
open import Data.Bool.BoolTheorems
open import Data.Char.Char
open import Data.Empty.Empty
open import Data.Fin.Fin
open import Data.Function.Function
open import Data.Isomorphism.Isomorphism
open import Data.List.List
open import Data.List.ListTheorems
open import Data.List.Relation.All
open import Data.List.Relation.Any
open import Data.List.Relation.Permutation
open import Data.List.Relation.Sorted
open import Data.List.Relation.Sublist
open import Data.List.Sorting.Extrinsic.InsertionSort
open import Data.List.Sorting.Extrinsic.InsertionSortTheorems
open import Data.List.Sorting.Extrinsic.LengthWF
open import Data.List.Sorting.Extrinsic.MergeBove
open import Data.List.Sorting.Extrinsic.MergeFuel
open import Data.List.Sorting.Extrinsic.MergeWF
open import Data.List.Sorting.Extrinsic.StalinSort
open import Data.List.Sorting.Intrinsic.InsertionSort
open import Data.List.Sorting.Intrinsic.Sorting
open import Data.Maybe.Maybe
open import Data.Nat.Div.DivBoveCapretta
open import Data.Nat.Div.DivFuel
open import Data.Nat.Div.DivWellFounded
open import Data.Nat.Div.DivIntrinsic
open import Data.Nat.Div.NonZero
open import Data.Nat.EvenOdd
open import Data.Nat.Le
open import Data.Nat.LeAlt
open import Data.Nat.Nat
open import Data.Nat.NatTheorems
open import Data.Product.Product
open import Data.Product.ProductTheorems
open import Data.Sigma.Sigma
open import Data.String.String
open import Data.Sum.Sum
open import Data.Sum.SumTheorems
open import Data.Unit.Unit
open import Data.Vec.Matrix
open import Data.Vec.Vec

open import Language.Printf.Printf
open import Language.Data.Data
open import Language.Exp.Intrinsic
open import Language.Exp.Extrinsic
open import Language.Lambda.Untyped
open import Language.Lambda.Typed

open import Prelude.Classes
open import Prelude.Nat

open import Relation.Equality.Propositional
open import Relation.Decidable.Dec
open import Relation.Induction.WellFounded
open import Relation.Induction.Natural
open import Relation.Induction.InverseImage
open import Relation.Induction.Lexicographic
