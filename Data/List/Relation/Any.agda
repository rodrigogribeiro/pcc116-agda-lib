module Data.List.Relation.Any where

open import Basics.Level

open import Data.List.List 

open import Relation.Equality.Propositional

-- any type

data Any {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)


infix 4 _∈_

_∈_ : ∀ {a}{A : Set a} → A → List A → Set a
x ∈ xs = Any (x ≡_) xs
