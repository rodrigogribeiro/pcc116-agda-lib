module Data.Product.ProductTheorems where

open import Basics.Admit

open import Data.Empty.Empty
open import Data.Isomorphism.Isomorphism
open import Data.Product.Product
open import Data.Unit.Unit

open import Relation.Equality.Propositional

-- product is commutative

×-comm : ∀ {l₁ l₂}{A : Set l₁}{B : Set l₂} →
         A × B ≃ B × A
×-comm
  = record { to = λ { (x , y) → y , x }
           ; from = λ { (x , y) → y , x }
           ; to∘from = λ { (x , y) → refl}
           ; from∘to = λ { (x , y) → refl} }

-- product is associative

×-assoc : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
            A × (B × C) ≃ (A × B) × C
×-assoc = admit

-- unit is an identity for product

×-identity-r : ∀ {l}{A : Set l} → A × ⊤ ≃ A
×-identity-r
  = record { to = λ { (x , tt) → x }
           ; from = λ x → x , tt
           ; to∘from = λ y → refl
           ; from∘to = λ { (x , tt) → refl} }

×-identity-l : ∀ {l}{A : Set l} → ⊤ × A ≃ A
×-identity-l = admit

-- currying

currying : ∀ {l₁ l₂ l₃}{A : Set l₁}{B : Set l₂}{C : Set l₃} →
           (A → B → C) ≃ ((A × B) → C)
currying
  = record { to = λ f → λ { (a , b) → f a b }
           ; from = λ f x y → f (x , y)
           ; to∘from = λ f → refl
           ; from∘to = λ f → refl }


-- ⊥ anula produtos

×-⊥-l : ∀ {l}{A : Set l} → ⊥ × A ≃ ⊥
×-⊥-l = admit

×-⊥-r : ∀ {l}{A : Set l} → A × ⊥ ≃ ⊥
×-⊥-r = admit
