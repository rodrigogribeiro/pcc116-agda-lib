module Data.Bool.Bool where

open import Equality.Propositional

-- basic boolean type definition

data Bool : Set where
   true  : Bool
   false : Bool


-- negation

not : Bool → Bool
not true  = false
not false = true


-- conjunction

infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false


-- exercise 1. Implement the disjunction operation on booleans.

infixr 6 _||_

_||_ : Bool → Bool → Bool
b || b' = {!!}

-- exercise 2. Implement the exclusive or operation on booleans.

infixl 6 _xor_

_xor_ : Bool → Bool → Bool
b xor b' = {!!}

-- exercise 3. Prove that conjunction is an associative operation

&&-assoc : (a b c : Bool) → (a && b) && c ≡ a && (b && c)
&&-assoc a b c = {!!}

-- exercise 4. Prove that disjunction is an associative operation

||-assoc : (a b c : Bool) → (a || b) || c ≡ a || (b || c)
||-assoc a b c = {!!}

-- exercise 5. Prove that conjunction is a commutative operation

&&-comm : (a b : Bool) → a && b ≡ b && a
&&-comm a b = {!!}

-- exercise 6. Prove that disjunction is a commutative operation

||-comm : (a b : Bool) → a || b ≡ b || a
||-comm a b = {!!}


-- exercise 7. Prove the following De Morgan law.

not-&& : (a b : Bool) → not (a && b) ≡ not a || not b
not-&& a b = {!!}


-- exercise 8. Prove the following De Morgan law.

not-|| : (a b : Bool) → not (a || b) ≡ not a && not b
not-|| a b = {!!}
