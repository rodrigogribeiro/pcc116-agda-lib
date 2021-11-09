module Data.Function.Function where

-- identity function

id : ∀ {l}{A : Set l} → A → A
id x = x

-- function composition

infixr 9 _∘_

_∘_ : ∀ {l1 l2 l3}
        {A : Set l1}
        {B : Set l2}
        {C : Set l3} →
        (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

flip : ∀ {l1 l2 l3}{A : Set l1}{B : Set l2}{C : Set l3} →
         (A → B → C) → (B → A → C)
flip f b a = f a b

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x
