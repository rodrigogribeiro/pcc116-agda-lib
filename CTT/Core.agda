{-# OPTIONS --cubical #-}
module CTT.Core where

open import Agda.Primitive.Cubical renaming ( primINeg  to ~_
                                            ; primHComp to trans
                                            )

-- definition of paths

postulate PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
{-# BUILTIN PATHP        PathP     #-}

infix 4 _≡_

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ i → A)

{-# BUILTIN PATH         _≡_     #-}


-- reflexivity

refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = λ i → x

-- symmetry

sym : ∀ {l}{A : Set l}{x y : A} → x ≡ y → y ≡ x
sym p = λ i → p (~ i)


-- congruence

cong : ∀ {A : Set}{B : A → Set}{x y : A}
       (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

-- function extensionality

funext : ∀ {l}{A B : Set l}{f g :  A → B}
           (p : ∀ a → f a ≡ g a) → f ≡ g
funext p = λ i a → p a i
