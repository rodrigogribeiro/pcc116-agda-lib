{-# OPTIONS --without-K #-}

module HTT.Basics.Sigma where

open import HTT.Basics.Universes
open import HTT.Basics.Id

record Σ {U V}{A : Type U}(B : A → Type V) : Type (U ⊔ V) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

_×_ : {U V : Universe} → Type U → Type V → Type (U ⊔ V)
A × B = Σ {A = A} (λ _ → B)

×-≡ : ∀ {U V}{A : Type U}{B : Type V}{x x' : A}{y y' : B} →
      x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
×-≡ refl refl = refl

×-≡-η : ∀ {U V}{A : Type U}{B : Type V}{z z' : A × B} →
          {p : z ≡ z'} → p ≡ ×-≡ (ap fst p) (ap snd p)
×-≡-η {p = refl} = refl

Σ-≡ : ∀ {U V}{A : Type U}{B : A → Type V}
        {p₁@(x , y) p₂@(x' , y') : Σ {A = A} B} →
        (p : x ≡ x') → (subst B p y) ≡ y' → p₁ ≡ p₂
Σ-≡ refl refl = refl


_↔_ : ∀ {U} → Type U → Type U → Type U
A ↔ B = (A → B) × (B → A)

inspect : ∀ {U}{A : Type U} (x : A) → Σ {A = A}(λ y → x ≡ y)
inspect x = x , refl
