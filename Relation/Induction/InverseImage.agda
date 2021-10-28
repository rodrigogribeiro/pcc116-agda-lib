open import Relation.Properties
open import Relation.Induction.WellFounded

module Relation.Induction.InverseImage {A B}(f : A → B)(_<_ : Relation B) where

_<<_ : Relation A
x << y = f x < f y

inv-img-acc : ∀ {x} → Acc _<_ (f x) → Acc _<<_ x
inv-img-acc (acc g) = acc (λ y fy<fx → inv-img-acc (g (f y) fy<fx))

inv-img-WF : WellFounded _<_ → WellFounded _<<_
inv-img-WF wf x = inv-img-acc (wf (f x))
