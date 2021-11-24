{-# OPTIONS --without-K #-}

module HTT.Univalence.IdProperties where

open import HTT.Basics.BasicTypes

-- relating ap and ∙

∙-ap : ∀ {U V}{A : Type U}{B : Type V}{x y z : A} →
         (f : A → B) → (p : x ≡ y) → (q : y ≡ z) →
         ap f (p ∙ q) ≡ ap f p ∙ ap f q
∙-ap f refl refl = refl


happly : ∀ {U V}{A : Type U}{B : Type V}
           {f g : A → B} → f ≡ g →
           (x : A) → f x ≡ g x
happly refl x = refl

coerce : ∀ {U}{A B : Type U} → A ≡ B → A → B
coerce refl x = x

-- ap, dependent version

apd : ∀ {U V}{A : Type U}{B : A → Type V}{x y : A} →
      (f : (x : A) → B x) → (p : x ≡ y) → subst B p (f x) ≡ f y
apd f refl = refl
