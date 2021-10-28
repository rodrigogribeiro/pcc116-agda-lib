open import Relation.Properties

module Relation.Induction.Lexicographic  {A B : Set}(_<A_ : Relation A)
                                                    (_<B_ : Relation B) where

open import Data.Product.Product
open import Relation.Induction.WellFounded

Pred : Set → Set₁
Pred A = A → Set

RecStruct : Set → Set₁
RecStruct A = Pred A → Pred A

WfRec : ∀ {A} → Relation A → RecStruct A
WfRec _<_ P x = ∀ y → y < x → P y


data _⊏_ : Relation (A × B) where
  left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : x₁ <A x₂) → (x₁ , y₁) ⊏ (x₂ , y₂)
  right : ∀ {x y₁ y₂}     (y₁<y₂ : y₁ <B y₂) → (x  , y₁) ⊏ (x  , y₂)


accessibleA : ∀ {x y} → Acc _<A_ x       →
                        WellFounded _<B_ →
                          Acc _⊏_ (x , y)

accessibleB : ∀ {x y} → Acc _<A_ x →
                         Acc _<B_ y →
                         WellFounded _<B_ →
                         WfRec _⊏_ (Acc _⊏_) (x , y)


accessibleA accA wfB
  = acc (accessibleB accA (wfB _) wfB)

accessibleB (acc IHA) accB wfB _ (left x₁<x₂)
  = accessibleA (IHA _ x₁<x₂) wfB
accessibleB accA (acc IHB) wfB _ (right y₁<y₂)
  = acc (accessibleB accA (IHB _ y₁<y₂) wfB)


wellFounded : WellFounded _<A_ → WellFounded _<B_ → WellFounded _⊏_
wellFounded wfA wfB p = accessibleA (wfA (proj₁ p)) wfB
