module Data.List.Sorting.Extrinsic.MergeBove where

open import Data.Nat.Nat
open import Data.List.List
open import Data.Product.Product
open import Prelude.Classes
open import Prelude.Nat
open import Relation.Induction.Natural
open import Relation.Induction.WellFounded
open import Data.List.Sorting.Extrinsic.MergeWF ℕ
open import Data.List.Sorting.Extrinsic.Merge hiding (merge)
open import Relation.Induction.Lexicographic renaming (_⊏_ to _⊑_)
open import Relation.Equality.Propositional

data _⊏_ : List ℕ → List ℕ → Set where
  ⊏-1 : ∀ {xs} → xs ⊏ []
  ⊏-2 : ∀ {ys} → [] ⊏ ys
  ⊏-3 : ∀ {x y xs ys} → x ≤ y → xs ⊏ (y ∷ ys) → (x ∷ xs) ⊏ (y ∷ ys)
  ⊏-4 : ∀ {x y xs ys} → x ≥ y → (x ∷ xs) ⊏ ys → (x ∷ xs) ⊏ (y ∷ ys)

merge-bove : {xs ys : List ℕ} → xs ⊏ ys → List ℕ
merge-bove {xs = xs} ⊏-1 = xs
merge-bove {ys = ys} ⊏-2 = ys
merge-bove {xs = x ∷ xs}(⊏-3 x≤y xs⊏ys) = x ∷ (merge-bove xs⊏ys)
merge-bove {ys = y ∷ ys}(⊏-4 x≥y xs⊏ys) = y ∷ (merge-bove xs⊏ys)

⊏-all : (xs ys : List ℕ) → xs ⊏ ys
⊏-all xs ys
  = wfRec _<*_
          merge-wf
          (λ p → proj₁ p ⊏ proj₂ p)
          step
          (xs , ys)
    where
      step : ∀ x → (∀ y → y <* x → proj₁ y ⊏ proj₂ y) → proj₁ x ⊏ proj₂ x
      step ([] , ys') IH = ⊏-2
      step (x ∷ xs' , []) IH = ⊏-1
      step (x ∷ xs' , y ∷ ys') IH with compare x y
      ...| less {{x≤y}}    = ⊏-3 x≤y (IH (xs' , y ∷ ys')
                                         (termination-1 xs' ys' x y))
      ...| equal {{refl}}  = ⊏-4 ≤-refl (IH (x ∷ xs' , ys')
                                            (termination-2 xs' ys' x y))
      ...| greater {{x≥y}} = ⊏-4 x≥y (IH (x ∷ xs' , ys')
                                         (termination-2 xs' ys' x y))

merge : List ℕ → List ℕ → List ℕ
merge xs ys = merge-bove (⊏-all xs ys)
