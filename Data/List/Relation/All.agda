module Data.List.Relation.All where

open import Basics.Admit
open import Basics.Level

open import Data.Biconditional.Biconditional
open import Data.List.List
open import Data.Product.Product

open import Relation.Decidable.Dec
open import Relation.Equality.Propositional

-- definition of All type

data All {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)


-- some results about All

All-++ : ∀ {a}{A : Set a}{P : A → Set a}(xs ys : List A) →
           All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++ xs ys = admit


All? : ∀ {a}{A : Set a}{P : A → Set a} → Decidable P → Decidable (All P)
All? decP = admit


