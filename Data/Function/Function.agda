module Data.Function.Function where

-- identity function

id : ∀ {l}{A : Set l} → A → A
id x = x

-- function composition

_∘_ : ∀ {l1 l2 l3}
        {A : Set l1}
        {B : Set l2}
        {C : Set l3} →
        (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

