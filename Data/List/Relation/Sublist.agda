module Data.List.Relation.Sublist where

open import Basics.Admit
open import Data.List.List

infix 20 _⊆_

data _⊆_ {l}{A : Set l} : List A → List A → Set l where
  stop : [] ⊆ []
  drop : ∀ {xs ys y} → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

⊆-refl : ∀ {l}{A : Set l}{xs : List A} → xs ⊆ xs
⊆-refl = admit

⊆-trans : ∀ {l}{A : Set l}{xs ys zs : List A} →
          xs ⊆ ys →
          ys ⊆ zs →
          xs ⊆ zs
⊆-trans = admit
