module Data.Vec.Vec where

open import Basics.Admit

open import Data.Fin.Fin
open import Data.Nat.Nat

data Vec {a}(A : Set a) : ℕ → Set a where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

head : ∀ {a}{A : Set a}{n} → Vec A (suc n) → A
head (x ∷ _) = x

_++_ : ∀ {a}{A : Set a}{n m} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b}{A : Set a}{B : Set b}{n} →
         (f : A → B)(xs : Vec A n)     →
         Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

nth : ∀ {a}{A : Set a}{n} → Fin n → Vec A n → A
nth zero      (x ∷ _)  = x
nth (suc idx) (_ ∷ xs) = nth idx xs

foldl : ∀ {a b}{A : Set a}{B : Set b}{n} → (B → A → B) → B → Vec A n → B
foldl _⊕_ v [] = v
foldl _⊕_ v (x ∷ xs) = foldl _⊕_ (v ⊕ x) xs

foldr : ∀ {a b}{A : Set a}{B : Set b}{n} → (A → B → B) → B → Vec A n → B
foldr _⊕_ v [] = v
foldr _⊕_ v (x ∷ xs) = x ⊕ foldr _⊕_ v xs

-- EXERCÍCIOS

-- utilities over vectors

zipWith : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}{n} →
            (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith = admit

pure : ∀ {a}{A : Set a}(x : A)(n : ℕ) → Vec A n
pure = admit

_⟨⋆⟩_ : ∀ {a b}{A : Set a}{B : Set b}{n} →
        Vec (A → B) n → Vec A n → Vec B n
_⟨⋆⟩_ = admit

tab : ∀ {a}{A : Set a} n → (Fin n → A) → Vec A n
tab = admit

reverse : ∀ {a}{A : Set a}{n} → Vec A n → Vec A n
reverse = admit
