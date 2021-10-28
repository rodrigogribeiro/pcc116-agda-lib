module Data.List.Sorting.Extrinsic.Merge where

open import Data.Nat.Nat
open import Data.List.List
open import Data.List.Sorting.Extrinsic.MergeWF ℕ
open import Data.Product.Product
open import Relation.Induction.WellFounded
open import Relation.Induction.Lexicographic
open import Prelude.Classes
open import Prelude.Nat
open import Relation.Induction.Natural

termination-1 : ∀ (xs ys : List ℕ) x y → (xs , y ∷ ys) <* (x ∷ xs , y ∷ ys)
termination-1 xs ys x y = left <-base

termination-2 : ∀ (xs ys : List ℕ) x y → (x ∷ xs , ys) <* (x ∷ xs , y ∷ ys)
termination-2 xs ys x y = right <-base

merge : List ℕ → List ℕ → List ℕ
merge xs ys = wfRec _<*_ merge-wf (λ _ → List ℕ) step (xs , ys)
  where
    step : ∀ (x : List ℕ × List ℕ) →
             (∀ y → y <* x → List ℕ) → List ℕ
    step ([] , ys') IH      = ys'
    step (x ∷ xs' , []) IH  = x ∷ xs'
    step (x ∷ xs' , y ∷ ys') IH with compare x y
    ...| less  = x ∷ IH (xs' , y ∷ ys') (termination-1 xs' ys' x y)
    ...| equal = y ∷ IH (x ∷ xs' , ys') (termination-2 xs' ys' x y)
    ...| greater = y ∷ IH (x ∷ xs' , ys') (termination-2 xs' ys' x y)
