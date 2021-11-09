module Data.Word.Word where

open import Data.Nat.Nat

postulate Word64 : Set
{-# BUILTIN WORD64 Word64 #-}

primitive
  primWord64ToNat   : Word64 → ℕ
  primWord64FromNat : ℕ → Word64
