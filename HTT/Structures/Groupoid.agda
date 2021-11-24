module HTT.Structures.Groupoid where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HSet


-- definition of a groupoid

isGroupoid : ∀ {U} → Type U → Type U
isGroupoid A = (x y : A) → isSet (x ≡ y)
