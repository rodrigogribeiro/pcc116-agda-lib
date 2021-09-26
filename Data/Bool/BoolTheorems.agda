module Data.Bool.BoolTheorems where

open import Basics.Admit
open import Data.Bool.Bool
open import Relation.Equality.Propositional

-- exercise 3. Prove that conjunction is an associative operation

&&-assoc : (a b c : Bool) → (a && b) && c ≡ a && (b && c)
&&-assoc a b c = admit

-- exercise 4. Prove that disjunction is an associative operation

||-assoc : (a b c : Bool) → (a || b) || c ≡ a || (b || c)
||-assoc a b c = admit

-- exercise 5. Prove that conjunction is a commutative operation

&&-comm : (a b : Bool) → a && b ≡ b && a
&&-comm a b = admit

-- exercise 6. Prove that disjunction is a commutative operation

||-comm : (a b : Bool) → a || b ≡ b || a
||-comm a b = admit


-- exercise 7. Prove the following De Morgan law.

not-&& : (a b : Bool) → not (a && b) ≡ not a || not b
not-&& a b = admit


-- exercise 8. Prove the following De Morgan law.

not-|| : (a b : Bool) → not (a || b) ≡ not a && not b
not-|| a b = admit
