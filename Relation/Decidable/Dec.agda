module Relation.Decidable.Dec where

open import Basics.Admit
open import Basics.Level

open import Data.Bool.Bool
open import Data.Empty.Empty
open import Data.Biconditional.Biconditional
open import Data.Product.Product
open import Data.Sum.Sum

open import Relation.Equality.Propositional

-- definition of the decidability predicate

data Dec {l}(A : Set l) : Set l where
  yes : A   → Dec A
  no  : ¬ A → Dec A

-- erasing decidability

⌞_⌟ : ∀ {l}{A : Set l} → Dec A → Bool
⌞ yes x ⌟ = true
⌞ no x ⌟  = false

-- lifting logic connectives to Dec

-- 1. conjunction

infixr 6 _×-dec_

_×-dec_ : ∀ {a b}{A : Set a}{B : Set b} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes x₁ = yes (x , x₁)
yes x ×-dec no x₁ = no (λ z → x₁ (proj₂ z))
no x ×-dec db = no (λ z → x (proj₁ z))

-- 2. disjunction

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
da ⊎-dec db = admit


-- 3. negation

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? d = admit

-- 4. implication

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
da →-dec db = admit

-- 5. biconditional

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
da ⇔-dec db = admit

-- erasure lemmas

&&-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ && ⌞ y ⌟ ≡ ⌞ x ×-dec y ⌟
&&-× x y = admit

||-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ || ⌞ y ⌟ ≡ ⌞ x ⊎-dec y ⌟
||-⊎ x y = admit

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌞ x ⌟ ≡ ⌞ ¬? x ⌟
not-¬ x = admit

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌞ x ⌟ iff ⌞ y ⌟ ≡ ⌞ x ⇔-dec y ⌟
iff-⇔ x y = admit

-- decidability

Decidable : ∀ {a b}{A : Set a} → (A → Set b) → Set (a ⊔ b)
Decidable {_}{_}{A} P = ∀ (x : A) → Dec (P x)
