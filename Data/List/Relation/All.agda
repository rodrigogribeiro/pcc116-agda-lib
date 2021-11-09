module Data.List.Relation.All where

open import Basics.Admit
open import Basics.Level

open import Data.Biconditional.Biconditional
open import Data.List.List
open import Data.List.Relation.Any
open import Data.Product.Product

open import Relation.Decidable.Dec
open import Relation.Equality.Propositional

-- definition of All type

data All {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)


lookup : ∀ {a b}{A : Set a}{P : A → Set b}{x xs} → x ∈ xs → All P xs → P x
lookup (here refl) (px ∷ Pxs) = px
lookup (there x∈xs) (px ∷ Pxs) = lookup x∈xs Pxs

updateWith : ∀ {a b}{A : Set a}{P : A → Set b}{x xs} → x ∈ xs → (P x → P x) → All P xs → All P xs
updateWith (here refl) f (x ∷ Pxs) = f x ∷ Pxs
updateWith (there x∈xs) f (x ∷ Pxs) = x ∷ updateWith x∈xs f Pxs

-- some results about All

All-++ : ∀ {a}{A : Set a}{P : A → Set a}(xs ys : List A) →
           All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++ xs ys = admit


All? : ∀ {a}{A : Set a}{P : A → Set a} → Decidable P → Decidable (All P)
All? decP = admit


