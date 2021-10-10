open import Algebra.Order.Order
open import Data.List.List
open import Data.Sum.Sum
open import Relation.Properties

module Data.List.Sorting.Extrinsic.InsertionSortTheorems {A : Set}
                                                         {_<_ : Relation A}
                                                         (M : IsTotalOrder _<_) where

open IsTotalOrder M
open import Data.List.Sorting.Extrinsic.InsertionSort M
open import Data.List.Relation.Permutation
open import Data.List.Relation.Sorted M


-- insertion sort sorts the input list.

insert-sorted : ∀ {xs}{x : A} → Sorted xs → Sorted (insert x xs)
insert-sorted {[]} empty = single
insert-sorted {([ x ])}{y} single with total M y x
...| inj₁ y<x = many y<x single
...| inj₂ x<y = many x<y single
insert-sorted {(x ∷ x' ∷ xs)}{y} (many x<x' sxs) with total M y x
...| inj₁ y<x = many y<x (many x<x' sxs)
...| inj₂ x<y with total M y x' | insert-sorted {x = y} sxs
...   | inj₁ y<x' | _ = many x<y (many y<x' sxs)
...   | inj₂ x'<y | p = many x<x' p

isort-sorted : ∀ (xs : List A) → Sorted (isort xs)
isort-sorted [] = empty
isort-sorted (x ∷ xs) = insert-sorted (isort-sorted xs)

-- insertion sort returns a permutation

insert-perm : ∀ {xs ys x} → xs ≈ ys → (x ∷ xs) ≈ (insert x ys)
insert-perm {.[]} {.[]} {x} empty = skip empty
insert-perm {(y ∷ ys)} {(.y ∷ zs)} {x} (skip p) with total M x y
...| inj₁ x≤y = skip (skip p)
...| inj₂ y≤x = ≈-trans swap (skip (insert-perm p))
insert-perm {x ∷ x' ∷ xs} {.x' ∷ .x ∷ ys} {z} swap with total M z x'
...| inj₁ z≤x' = skip swap
...| inj₂ x'≤z with total M z x
...    | inj₁ z≤x = ≈-sym (≈-trans swap (skip swap))
...    | inj₂ x≤z = ≈-sym (≈-trans swap (≈-sym (≈-trans swap (skip (≈-trans swap (skip (insert-perm ≈-refl)))))))
insert-perm {xs} {ys} {x} (≈-trans p p₁) = ≈-trans (skip p) (insert-perm p₁)

isort-perm : (xs : List A) → xs ≈ (isort xs)
isort-perm [] = empty
isort-perm (x ∷ xs) = insert-perm (isort-perm xs)
