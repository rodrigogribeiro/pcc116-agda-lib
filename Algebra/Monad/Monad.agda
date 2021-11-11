module Algebra.Monad.Monad where

open import Algebra.Functor.Functor

record Monad (M : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B
  _>>_ : ∀ {A B} → M A → M B → M B
  m >> m' = m >>= λ _ → m'

open Monad {{...}} public


monadAp : ∀ {a b} {A B : Set a} {M : Set a → Set b}
            {{_ : Functor M}} →
            (M (A → B) → ((A → B) → M B) → M B) →
            M (A → B) → M A → M B
monadAp _>>=_ mf mx = mf >>= λ f → fmap f mx
