module Equality.Propositional where

-- definition of the propositional equality type

infix 4 _≡_

data _≡_ {l}{A : Set l}(x : A) : A → Set l where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}


-- definition of an equality relation

trans : ∀ {l}{A : Set l}{x y z : A} →
        x ≡ y →
        y ≡ z →
        x ≡ z
trans refl refl = refl

sym : ∀ {l}{A : Set l}{x y : A} →
      x ≡ y →
      y ≡ x
sym refl = refl

-- equality chain operators

infix 1 begin_

begin_ : ∀ {l}{A : Set l}{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

infixr 2 _≡⟨⟩_

_≡⟨⟩_ : ∀ {l}{A : Set l}(x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infixr 2 step-≡ 

step-≡ : ∀ {l}{A : Set l}(x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

infix 3 _∎

_∎ : ∀ {l}{A : Set l}(x : A) → x ≡ x
_∎ _ = refl

-- congruence

cong : ∀ {l l'}{A : Set l}{B : Set l'}{x y : A}(f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
