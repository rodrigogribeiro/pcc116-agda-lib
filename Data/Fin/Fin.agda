module Data.Fin.Fin where

open import Data.Empty.Empty
open import Data.Isomorphism.Isomorphism
open import Data.Nat.Nat
open import Data.Unit.Unit

open import Relation.Equality.Propositional

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

-- isomorfismos

Fin0≃⊥ : Fin 0 ≃ ⊥
Fin0≃⊥
  = record {
       to = λ ()
    ; from = λ ()
    ; to∘from = λ ()
    ; from∘to = λ () }


Fin1≃⊤ : Fin 1 ≃ ⊤
Fin1≃⊤
  = record {
      to = λ _ → tt
    ; from = λ _ → zero
    ; to∘from = λ {tt → refl}
    ; from∘to = λ {zero → refl} }
