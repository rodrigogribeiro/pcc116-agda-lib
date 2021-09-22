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

-- remaining exercises are in file Bool-Theorems
