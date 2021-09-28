module Data.Sigma.Sigma where

open import Basics.Level

open import Data.Sum.Sum
open import Data.Isomorphism.Isomorphism

open import Relation.Equality.Propositional

-- dependent products

record Σ {l₁ l₂} (A : Set l₁) (B : A → Set l₂) : Set (l₁ ⊔ l₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public


-- existential quantifier

∃ : ∀ {l₁ l₂}{A : Set l₁}(B : A → Set l₂) → Set (l₁ ⊔ l₂)
∃ {A = A} B = Σ A B

-- syntax for existentials

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- distributivity over sums

∃-⊎ : ∀ {l₁ l₂}{A : Set l₁}{B C : A → Set l₂} →
        ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-⊎
  = record { to = λ{ (x , inj₁ bx) → inj₁ (x , bx) ;
                     (x , inj₂ cx) → inj₂ (x , cx) }
           ; from = λ{ (inj₁ (x , bx)) → x , inj₁ bx  ;
                       (inj₂ (x , cx)) → x , inj₂ cx }
           ; to∘from = λ { (inj₁ (x , bx)) → refl ;
                           (inj₂ (x , cx)) → refl} 
           ; from∘to = λ { (x , inj₁ bx) → refl ;
                            (x , inj₂ cx) → refl } }
