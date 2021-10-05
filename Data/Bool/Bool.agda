module Data.Bool.Bool where

open import Basics.Admit

open import Data.Empty.Empty
open import Data.Unit.Unit

open import Relation.Equality.Propositional

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
b || b' = admit

-- exercise 2. Implement the exclusive or operation on booleans.

infixl 6 _xor_

_xor_ : Bool → Bool → Bool
b xor b' = admit

-- boolean implication

_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false


-- biconditional on booleans

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
_     iff _     = false

-- lifting booleans into evidence

T : Bool → Set 
T true  = ⊤
T false = ⊥

T→≡ : (b : Bool) → T b → b ≡ true
T→≡ true  tt = refl
T→≡ false ()

≡→T : {b : Bool} → b ≡ true → T b
≡→T refl = tt


-- if construction

infix 0 if_then_else_

if_then_else_ : ∀ {a}{A : Set a} → Bool → A → A → A
if true  then v else _ = v
if false then _ else v = v
