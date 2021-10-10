module Data.List.Relation.Any where

open import Basics.Admit
open import Basics.Level

open import Data.Biconditional.Biconditional
open import Data.List.List 

open import Relation.Decidable.Dec
open import Relation.Equality.Propositional

-- any type

data Any {a b}{A : Set a}(P : A → Set b) : List A → Set (a ⊔ b) where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)


infix 4 _∈_

_∈_ : ∀ {a}{A : Set a} → A → List A → Set a
x ∈ xs = Any (x ≡_) xs

Any-++ˡ : ∀ {a b}{A : Set a}{P : A → Set b}{xs ys : List A} → Any P xs → Any P (ys ++ xs)
Any-++ˡ = admit

Any-++ʳ : ∀ {a b}{A : Set a}{P : A → Set b}{xs ys : List A} → Any P xs → Any P (xs ++ ys)
Any-++ʳ = admit

Any-++-comm : ∀ {a b}{A : Set a}{P : A → Set b}{xs ys : List A} →
                Any P (xs ++ ys) ⇔ Any P (ys ++ xs)
Any-++-comm = admit

AnyDec : ∀ {a b}{A : Set a}{P : A → Set b} → Decidable P → Decidable (Any P)
AnyDec decP = admit
