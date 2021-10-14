module Data.String.String where

open import Data.Bool.Bool
open import Data.Char.Char
open import Data.List.List hiding (_++_)
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Sigma.Sigma

postulate String : Set

{-# BUILTIN STRING String #-}

primitive
  primStringUncons   : String → Maybe (Σ Char (λ _ → String))
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowChar       : Char → String
  primShowString     : String → String
  primShowNat        : ℕ → String


stringToList : String → List Char
stringToList = primStringToList

stringFromList : List Char → String
stringFromList = primStringFromList

ℕtoString : ℕ → String
ℕtoString = primShowNat

_++_ : String → String → String
_++_ = primStringAppend
