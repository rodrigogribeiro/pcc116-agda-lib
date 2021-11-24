module HTT.Results.Choice where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HSet
open import HTT.Structures.HProp
open import HTT.Structures.Existential
open import HTT.Structures.Truncation

-- constructive axiom of choice

CAC : ∀ {U V W} → Type (((U ⁺) ⊔ (V ⁺)) ⊔ (W ⁺))
CAC {U}{V}{W} = {A : Type U}{B : Type V}
                (R : A → B → Type W) →
                (r : (x : A) → Σ {A = B} (λ y → R x y)) →
                Σ {A = (A → B)}(λ f → (x : A) → R x (f x))

cac : ∀ {U V W} → CAC {U} {V} {W}
cac R f = (λ x → fst (f x)) , (λ x → snd (f x))


-- axiom of choice

AC : ∀ {U V W} → Type (((U ⁺) ⊔ (V ⁺)) ⊔ (W ⁺))
AC {U}{V}{W} = {A : Type U}{B : Type V} →
               isSet A →
               isSet B →
               (R : A → B → Type W) →
               ((x : A)(y : B) → isProp (R x y)) →
               (r : (x : A) → ∃ B (λ y → R x y)) →
               ∃ (A → B)(λ f → (x : A) → R x (f x))

-- other formulation

PAC : ∀ {U V} → Type ((U ⁺) ⊔ (V ⁺))
PAC {U}{V} = {A : Type U}{B : A → Type V} →
             ((x : A) → ∥ B x ∥) → ∥ ((x : A) → B x) ∥
