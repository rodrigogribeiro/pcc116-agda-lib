module Data.List.Relation.Permutation where


open import Data.List.List

infix 4 _≈_

data _≈_ {a}{A : Set a} : List A → List A → Set a where
  empty : [] ≈ []
  skip  : ∀ {x xs ys} → xs ≈ ys
                      → (x ∷ xs) ≈ (x ∷ ys)
  swap  : ∀ {x y xs} → (x ∷ y ∷ xs) ≈ (y ∷ x ∷ xs)
  ≈-trans : ∀ {xs ys zs} → xs ≈ ys
                         → ys ≈ zs
                         → xs ≈ zs

≈-refl : ∀ {a}{A : Set a}{xs : List A} → xs ≈ xs
≈-refl {xs = []} = empty
≈-refl {xs = x ∷ xs} = skip ≈-refl

≈-sym : ∀ {a}{A : Set a}{xs ys : List A} → xs ≈ ys → ys ≈ xs
≈-sym empty = empty
≈-sym (skip xs≈ys) = skip (≈-sym xs≈ys)
≈-sym swap = swap
≈-sym (≈-trans xs≈ys xs≈ys₁) = ≈-trans (≈-sym xs≈ys₁) (≈-sym xs≈ys)
