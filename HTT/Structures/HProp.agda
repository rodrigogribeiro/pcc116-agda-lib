{-# OPTIONS --without-K #-}

module HTT.Structures.HProp where

open import HTT.Basics.BasicTypes

-- definition of when a type is a proposition

isProp : ∀ {U} → Type U → Type U
isProp A = (x y : A) → x ≡ y

-- the empty type is a proposition

⊥-isProp : isProp ⊥
⊥-isProp ()

-- the unit type is a proposition

⊤-isProp : isProp ⊤
⊤-isProp ⋆ ⋆ = refl

-- theorem: boolean type is not a proposition

Bool-isnt-Prop : ¬ (isProp Bool)
Bool-isnt-Prop p with p true false
...| ()

-- definition of hProps

hProp : ∀ U → Type (U ⁺)
hProp I = Σ {A = Type I} isProp

-- products

Σ-isProp : ∀ {U V}{A : Type U}{B : A → Type V} →
           ((x : A) → isProp (B x)) →
           ((x y : A) → B x → B y → x ≡ y) → isProp (Σ B)
Σ-isProp f g (a , b) (a' , b') with g a a' b b'
...| refl with f a b b'
...   | refl = refl

×-isProp : ∀ {U V}{A : Type U}{B : Type V} →
             isProp A → isProp B → isProp (A × B)
×-isProp PA PB (a , b) (a' , b') with PA a a' | PB b b'
...| refl | refl = refl

-- functions

→-isProp : ∀ {U V}{A : Type U}{B : Type V} → isProp B → isProp (A → B)
→-isProp PB f g = extensionality (λ x → PB (f x) (g x))

-- pi types

Π-isProp : ∀ {U V}{A : Type U}{B : A → Type V} →
             ((x : A) → isProp (B x)) →
             isProp ((x : A) → B x)
Π-isProp PB f g = extensionality (λ x → PB x (f x) (g x))

-- ≤ is a prop

≤-isProp : ∀ {n m : ℕ} → isProp (n ≤ m)
≤-isProp {.0} {m} z≤n z≤n = refl
≤-isProp {.(suc _)} {.(suc _)} (s≤s p) (s≤s q) = ap s≤s (≤-isProp p q)

-- negation

¬-isProp : ∀ {U}{A : Type U} → isProp (¬ A)
¬-isProp = →-isProp ⊥-isProp

-- sum

+-isProp : ∀ {U V}{A : Type U}{B : Type V} →
             isProp A →
             isProp B →
             (A → B → ⊥) →
             isProp (A + B)
+-isProp PA PB A→B→⊥ (inl x) (inl y) = ap inl (PA x y)
+-isProp PA PB A→B→⊥ (inl x) (inr y) = ⊥-elim (A→B→⊥ x y)
+-isProp PA PB A→B→⊥ (inr x) (inl y) = ⊥-elim (A→B→⊥ y x)
+-isProp PA PB A→B→⊥ (inr x) (inr y) = ap inr (PB x y)

-- isDec is a proposition

isDec-isProp : ∀ {U}{A : Type U} → isProp A → isProp (isDec A)
isDec-isProp PA = +-isProp PA ¬-isProp (λ a ¬a → ¬a a)

-- predicates

isPred : ∀ {U V}{A : Type U} → (A → Type V) → Type (U ⊔ V)
isPred {A = A} P = (x : A) → isProp (P x)


-- classical logic

module Classical where

  LEM : ∀ {U} → Type (U ⁺)
  LEM {U} = {A : Type U} → isProp A → A + (¬ A)

  NNE : ∀ {U} → Type (U ⁺)
  NNE {U} = {A : Type U} → isProp A → ¬ (¬ A) → A


-- propositions are sets

open import HTT.Structures.HSet

aProp-is-Set-lem : ∀ {U}{A : Type U}{x y : A} → (P : isProp A) →
                     (z : A)(p : x ≡ y) → p ≡ (! (P z x)) ∙ (P z y)
aProp-is-Set-lem {x = x} P z refl = ! ∙-cancel-right (P z x)

aProp-is-Set : ∀ {U}{A : Type U} → isProp A → isSet A
aProp-is-Set {A = A} P x y p q = aProp-is-Set-lem P x p ∙ (! aProp-is-Set-lem P x q)

isProp-isProp : ∀ {U}{A : Type U} → isProp (isProp A)
isProp-isProp {U = U} f g = extensionality2 (λ x y → aProp-is-Set f x y (f x y) (g x y))

PE : ∀ {U} → Type (U ⁺)
PE {U} = {A B : Type U} → isProp A → isProp B → A ↔ B → A ≡ B
