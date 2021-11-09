module Algebra.Monad.Monad where

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B
  _>>_ : ∀ {A B} → M A → M B → M B
  m >> m' = m >>= λ _ → m'

open Monad {{...}} public
