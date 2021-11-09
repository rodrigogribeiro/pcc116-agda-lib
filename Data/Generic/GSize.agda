module Data.Generic.GSize where

open import Basics.Admit
open import Data.Generic.Regular
open import Data.Nat.Nat

-- desenvolva uma função para contar o número de elementos
-- presentes em uma estrutura de dados qualquer.

gsize : ∀ {n}{Γ : Ctx n}{t : Reg n} → Data Γ t → ℕ
gsize = admit
