module Data.Nat.Div.DivWellFounded where

open import Data.Nat.Nat
open import Data.Nat.Div.NonZero

open import Relation.Induction.WellFounded
open import Relation.Induction.Natural

div : (n m : ℕ){{_ : NonZero m}} → ℕ
div n m = wfRec _<_         -- relação de ordem
                <-ℕ-wf      -- prova de well-foundness
                (λ _ → ℕ)  -- tipo de retorno
                step        -- corpo da função
                n           -- entrada
    where
      step : ∀ (x : ℕ) → ((y : ℕ) → y < x → ℕ) → ℕ
      step zero    IH = 0
      step (suc x) IH = suc (IH (x - m) (n-m<n+1 x m))
