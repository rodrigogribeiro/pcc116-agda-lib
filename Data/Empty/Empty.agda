module Data.Empty.Empty where

-- empty type 

data ⊥ : Set where


-- elimination

⊥-elim : ∀ {l}{A : Set l} → ⊥ → A
⊥-elim ()


-- negation

infix 3 ¬_

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥

