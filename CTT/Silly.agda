{-# OPTIONS --cubical #-}


module CTT.Silly where

open import CTT.Core

-- silly definition of lists as a HIT

data SList (A : Set) : Set where
  [] : SList A
  _∷_ : A → SList A → SList A
  silly : ∀ x xs → x ∷ xs ≡ xs

variable A : Set

postulate admit : ∀ {A : Set} → A


-- Exercise 1: prove the following path

slist≡[] : (xs : SList A) → xs ≡ []
slist≡[] = admit

-- Exercise 2: define the append operation on slists

_++s_ : (xs ys : SList A) → SList A
xs ++s ys = admit

-- Exercise 3: prove the following property of append

++s-silly : (xs ys : SList A) → xs ++s ys ≡ ys
++s-silly = admit
