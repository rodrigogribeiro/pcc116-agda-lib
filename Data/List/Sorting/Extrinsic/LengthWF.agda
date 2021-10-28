module Data.List.Sorting.Extrinsic.LengthWF (A : Set) where

open import Data.List.List
open import Relation.Induction.Natural
open import Relation.Induction.InverseImage (length {A = A}) _<_ public
open import Relation.Induction.WellFounded

length-wf : WellFounded _<<_
length-wf = inv-img-WF <-ℕ-wf
