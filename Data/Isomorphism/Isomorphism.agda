module Data.Isomorphism.Isomorphism where

open import Basics.Level
open import Data.Function.Function
open import Relation.Equality.Propositional

-- definition of isomorfism

infix 0 _≃_

record _≃_ {l}{l'}(A : Set l)(B : Set l') : Set (l ⊔ l') where
  field
    to   : A → B
    from : B → A
    to∘from : ∀ (y : B) → (to ∘ from) y ≡ y
    from∘to : ∀ (x : A) → (from ∘ to) x ≡ x

open _≃_ public


-- isomorfism is an equivalence relation

≃-refl : ∀ {l}{A : Set l} → A ≃ A
≃-refl
  = record { to = id
           ; from = id
           ; to∘from = λ y → refl
           ; from∘to = λ x → refl }


≃-sym : ∀ {l l'}{A : Set l}{B : Set l'}
        → A ≃ B → B ≃ A
≃-sym A≃B
  = record { to = from A≃B
           ; from = to A≃B
           ; to∘from = from∘to A≃B
           ; from∘to = to∘from A≃B }

≃-trans : ∀ {l₁ l₂ l₃}
            {A : Set l₁}
            {B : Set l₂}
            {C : Set l₃} →
            A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C
  = record { to = to B≃C ∘ to A≃B
           ; from = from A≃B ∘ from B≃C
           ; to∘from = λ {y →
             begin
               (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
             ≡⟨⟩
               to B≃C (to A≃B (from A≃B (from B≃C y)))
             ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
               to B≃C (from B≃C y)
             ≡⟨ to∘from B≃C y ⟩
               y
             ∎}
           ; from∘to = λ {y →
             begin
               (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) y)
             ≡⟨⟩
               (from A≃B (from B≃C (to B≃C (to A≃B y))))
             ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B y)) ⟩
               from A≃B (to A≃B y)
             ≡⟨ from∘to A≃B y ⟩
               y
             ∎} }

-- equational reasoning for isomorphism

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
      → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ {l₁ l₂ l₃}(A : Set l₁)
                       {B : Set l₂}
                       {C : Set l₃} → 
       A ≃ B → B ≃ C → A ≃ C
  _ ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

