module Relation.Induction.WellFounded where

open import Relation.Properties

data Acc {A : Set}(_<_ : Relation A)(x : A) : Set where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set}(_<_ : Relation A) → Set
WellFounded _<_ = ∀ x → Acc _<_ x

acc-fold : {A : Set}                             →
           {_<_ : Relation A}                    →
           {P : A → Set}                        →
           (∀ x → (∀ y → y < x → P y) → P x) →
           ∀ z → Acc _<_ z → P z
acc-fold IH z (acc H) = IH z (λ y y<z → acc-fold IH y (H y y<z))


wfRec : {A : Set}                             →
        (_<_ : Relation A)                    →
        WellFounded _<_                       →
        ∀ (P : A → Set)                      →
        (∀ x → (∀ y → y < x → P y) → P x) →
        ∀ a → P a
wfRec R wf P IH a = acc-fold IH a (wf a)
