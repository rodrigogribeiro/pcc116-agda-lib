{-# OPTIONS --without-K #-}
module HTT.Structures.Truncation where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HProp

-- postulating propositional truncation

postulate ∥_∥ : ∀ {U} → Type U → Type U
postulate ∥∥-isProp : ∀ {U}(A : Type U) → isProp ∥ A ∥

-- introduction

postulate ∣_∣ : ∀ {U}{A : Type U} → A → ∥ A ∥

-- elimination

postulate ∥∥-rec : ∀ {U V}{A : Type U}{B : Type V} →
                   isProp B → (A → B) → (∥ A ∥ → B)

-- computation

postulate ∥∥-comp : ∀ {U V}{A : Type U}{B : Type V} →
                    (P : isProp B)(f : A → B)(x : A) →
                    ∥∥-rec P f ∣ x ∣ ≡ f x

postulate ∥∥-eta : ∀ {U}{A : Type U}(P : isProp A)(x : ∥ A ∥) →
                   ∣ ∥∥-rec P (λ x → x) x ∣ ≡ x

-- propositional extensionality

postulate propExtensionality : ∀ {U}{A : Type U}(p q : isProp ∥ A ∥) → p ≡ q
