open import Algebra.Order.Order
open import Basics.Admit
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties


module Data.List.Sorting.Extrinsic.StalinSort {A : Set}
                                              {_<_ : Relation A}
                                              (M : IsTotalOrder _<_) where

open IsTotalOrder M public

{-
O objetivo deste exercício é a definição do algoritmo de
ordenação StalinSort que consiste em percorrer uma lista removendo
elementos que estão fora de ordem. O resultado final será uma lista ordenada.
-}

stalinSort : List A → List A
stalinSort = admit
