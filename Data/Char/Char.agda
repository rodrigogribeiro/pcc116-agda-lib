module Data.Char.Char where

open import Data.Bool.Bool
open import Data.Nat.Nat

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii primIsLatin1 primIsPrint primIsHexDigit : Char → Bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → Bool


_≟_ : Char → Char → Bool
_≟_ = primCharEquality

ℕtoChar : ℕ → Char
ℕtoChar = primNatToChar
