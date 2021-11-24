{-# OPTIONS --without-K #-}

module HTT.Basics.Extensionality where

open import HTT.Basics.Id
open import HTT.Basics.Universes


-- definition of function extensionality

DFE : (U V : Universe) → Type ((U ⊔ V) ⁺)
DFE U V = {A : Type U}{B : A → Type V}
          {f g : (x : A) → B x} →
          ((x : A) → f x ≡ g x) → f ≡ g

postulate extensionality : {U V : Universe} → DFE U V

DFE2 : (U V W : Universe) → Type ((U ⊔ V ⊔ W) ⁺)
DFE2 U V W = {A : Type U}{B : A → Type V}{C : {x : A} → B x → Type W}
             {f g : (x : A) → (b : B x) → C b} → ((x : A) → (y : B x) → f x y ≡ g x y) → f ≡ g

postulate extensionality2 : {U V W : Universe} → DFE2 U V W
