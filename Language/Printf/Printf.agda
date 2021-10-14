module Language.Printf.Printf where

open import Data.Char.Char
open import Data.Function.Function
open import Data.List.List
open import Data.Nat.Nat
open import Data.String.String hiding (_++_)

-- format syntax

data Format : Set where
  ℕ-Format : Format     → Format
  S-Format : Format     → Format
  Literal  : (c : Char) → Format → Format
  Empty    : Format

-- parsing format

parseFormat : List Char → Format
parseFormat ('%' ∷ 'n' ∷ cs) = ℕ-Format (parseFormat cs)
parseFormat ('%' ∷ 's' ∷ cs) = S-Format (parseFormat cs)
parseFormat (c ∷ cs) = Literal c (parseFormat cs)
parseFormat [] = Empty

-- format semantics

⟦_⟧F : Format → Set
⟦ ℕ-Format f ⟧F  = ℕ      → ⟦ f ⟧F
⟦ S-Format f ⟧F  = String → ⟦ f ⟧F
⟦ Literal c f ⟧F = ⟦ f ⟧F
⟦ Empty ⟧F       = String

-- printf type

Printf : String → Set
Printf = ⟦_⟧F ∘ parseFormat ∘ stringToList

-- printf interpreter

showNat : ℕ → List Char
showNat = stringToList ∘ ℕtoString

interpFormat : List Char → (f : Format) → ⟦ f ⟧F
interpFormat s (ℕ-Format f)
  = λ n → interpFormat (s ++ showNat n) f
interpFormat s (S-Format f)
  = λ s' → interpFormat (s ++ (stringToList s')) f
interpFormat s (Literal c f)
  = interpFormat (s ++ [ c ]) f
interpFormat s Empty = (stringFromList s)


-- printf top level function

printf : (s : String) → Printf s
printf s = interpFormat [] (parseFormat (stringToList s))
