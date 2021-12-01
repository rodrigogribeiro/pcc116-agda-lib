{-# OPTIONS --without-K #-}

module HTT.Results.Incompatibility where

open import HTT.Basics.BasicTypes
open import HTT.Results.Hedberg
open import HTT.Structures.HSet
open import HTT.Univalence.IdProperties
open import HTT.Univalence.Equivalence
open import HTT.Univalence.Axiom

-- 1. type is not a set

not-inv : (b : Bool) → not (not b) ≡ b
not-inv false = refl
not-inv true  = refl

false≢true : ¬ (false ≡ true)
false≢true ()

not-≃ : Bool ≃ Bool
not-≃ = not , ((not , not-inv) , (not , not-inv))


Type-isntSet : ¬ (isSet (Type U₀))
Type-isntSet S = false≢true contra
  where
    contra : false ≡ true
    contra = begin
               false
             ≡⟨ happly (ap coerce (S Bool Bool refl (ua not-≃))) false ⟩
               coerce (ua not-≃) false
             ≡⟨ happly (ua-comp not-≃) false ⟩
               true
             ∎

-- incompatibility of UIP

UIP : ∀ {U} → Type (U ⁺)
UIP {U} = ∀ {A : Type U}{x y : A}(p q : x ≡ y) → p ≡ q

¬UIP : (∀ {U} → UIP {U}) → ⊥
¬UIP uip = Type-isntSet (λ _ _ → uip)

-- incompatibility of double negation

¬NNE : (∀ {U}{A : Type U} →  (¬ (¬ A) → A)) → ⊥
¬NNE nne = Type-isntSet (Hedberg (λ x y → nne {A = x ≡ y}))
