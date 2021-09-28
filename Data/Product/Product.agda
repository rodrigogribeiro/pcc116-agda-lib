module Data.Product.Product where

open import Basics.Level

-- definition of product types (conjunction)

infixr 2 _×_
infixr 4 _,_

record _×_ {l₁ l₂}
           (A : Set l₁)
           (B : Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

