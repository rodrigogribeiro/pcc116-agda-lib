module Data.Sum.SumTheorems where

open import Basics.Admit

open import Data.Empty.Empty
open import Data.Function.Function
open import Data.Isomorphism.Isomorphism
open import Data.Product.Product
open import Data.Sum.Sum
open import Data.Unit.Unit

open import Relation.Equality.Propositional


-- sum is commutative

⊎-comm : ∀ {l₁ l₂}{A : Set l₁}{B : Set l₂} →
           A ⊎ B ≃ B ⊎ A
⊎-comm = admit

-- sum is an associative operation

⊎-assoc : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
          A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc
  = record { to = ⊎-elim (inj₁ ∘ inj₁)
                         (⊎-elim (inj₁ ∘ inj₂)
                                 inj₂)
           ; from = ⊎-elim (⊎-elim inj₁ (inj₂ ∘ inj₁))
                           (inj₂ ∘ inj₂)
           ; to∘from = λ { (inj₁ (inj₁ a)) → refl ;
                           (inj₁ (inj₂ b)) → refl ;
                           (inj₂ c) → refl}
           ; from∘to = λ { (inj₁ a) → refl ;
                            (inj₂ (inj₁ b)) → refl ;
                            (inj₂ (inj₂ c)) → refl } }

-- empty is an unit for sum 

⊎-identity-r : ∀ {l}{A : Set l} → A ⊎ ⊥ ≃ A
⊎-identity-r
  = record { to = ⊎-elim id ⊥-elim
           ; from = inj₁
           ; to∘from = λ y → refl
           ; from∘to = λ { (inj₁ a) → refl ;
                           (inj₂ ())} }

⊎-identity-l : ∀ {l}{A : Set l} → ⊥ ⊎ A ≃ A
⊎-identity-l = admit
