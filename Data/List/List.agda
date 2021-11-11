module Data.List.List where

open import Algebra.Monoid.Monoid

open import Basics.Level

open import Data.Bool.Bool
open import Data.Function.Function
open import Data.Maybe.Maybe hiding (map)
open import Data.Nat.Nat
open import Data.Product.Product


-- definition of lists

infixr 5 _∷_
  
data List {a}(A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

{-# BUILTIN LIST List #-}

-- syntax sugar for lists

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- basic list functions

length : ∀ {a}{A : Set a} → List A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

infixr 5 _++_

_++_ : ∀ {a}{A : Set a} → List A → List A → List A
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- map functions

map : ∀ {a b}{A : Set a}{B : Set b} →
        (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- list reverse

reverse : ∀ {a}{A : Set a} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

-- foldr operator

foldr : ∀ {a b}{A : Set a}{B : Set b} →
          (A → B → B) → B → List A → B
foldr _ v []       = v
foldr f v (x ∷ xs) = f x (foldr f v xs) 

-- foldl operator

foldl : ∀ {a b}{A : Set a}{B : Set b} → 
          (B → A → B) → B → List A → B
foldl _ v []       = v
foldl f v (x ∷ xs) = foldl f (f v x) xs

-- filter

filter : ∀ {a}{A : Set a} → (A → Bool) → List A → List A
filter p []       = []
filter p (x ∷ xs) = let r = filter p xs
                    in if p x then x ∷ r else r

-- zip and unzip

zip : ∀ {a b}{A : Set a}{B : Set b} → List A → List B → List (A × B)
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

unzip : ∀ {a b}{A : Set a}{B : Set b} → List (A × B) → (List A) × (List B)
unzip [] = ([] , [])
unzip (p ∷ ps) = let r = unzip ps
                 in (proj₁ p ∷ proj₁ r , proj₂ p ∷ proj₂ r)

-- nth function

nth : ∀ {a}{A : Set a} → ℕ → List A → Maybe A
nth _       []       = nothing
nth 0       (x ∷ xs) = just x
nth (suc n) (x ∷ xs) = nth n xs

-- repeat

repeat : ∀ {a}{A : Set a} → A → ℕ → List A
repeat x zero    = []
repeat x (suc n) = x ∷ repeat x n


-- concatMap

concat : ∀ {a}{A : Set a} → List (List A) → List A
concat = foldr _++_ []

concatMap : ∀ {a b}{A : Set a}{B : Set b} → (A → List B) → List A → List B
concatMap f = concat ∘ map f
