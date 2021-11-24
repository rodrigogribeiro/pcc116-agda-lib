{-# OPTIONS --without-K #-}

module HTT.Basics.Empty where

open import HTT.Basics.Universes

-- empty type

data ⊥ : Type U₀ where

¬_ : {U : Universe} → Type U → Type U
¬ A = A → ⊥

-- elimination

⊥-elim : ∀ {U}{A : Type U} → ⊥ → A
⊥-elim ()
