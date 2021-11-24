{-# OPTIONS --without-K #-}

module HTT.Basics.Id where

open import HTT.Basics.Universes

variable U : Universe

data Id (A : Type U) : A → A → Type U where
  refl : {x : A} → Id A x x

{-# BUILTIN EQUALITY Id #-}

infix 4 _≡_

_≡_ : {A : Type U} → A → A → Type U
x ≡ y = Id _ x y

ap : ∀ {V}{A : Type U}{B : Type V}{x y : A}(f : A → B) →
       x ≡ y → f x ≡ f y
ap f refl = refl

ap2 : ∀ {V W}{A : Type U}{B : Type V}{C : Type W}
        {x x' : A}{y y' : B}(f : A → B → C) →
        x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap2 f refl refl = refl

subst : ∀ {U V}{A : Type U}(P : A → Type V){x y : A} →
          x ≡ y → P x → P y
subst P refl px = px

subst2 : ∀ {U V W}{A : Type U}{B : Type V}(P : A → B → Type W){x y : A}{x' y' : B} →
          x ≡ y → x' ≡ y' → P x x' → P y y'
subst2 P refl refl px = px

-- Definition of the groupoid structure of types.

-- composition

infixl 6 _∙_

_∙_ : {A : Type U}{x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

∙-id-left : {A : Type U}{x y : A} →
            (p : x ≡ y) → refl ∙ p ≡ p
∙-id-left p = refl

∙-id-right : {A : Type U}{x y : A} →
             (p : x ≡ y) → p ∙ refl ≡ p
∙-id-right refl = refl

∙-assoc : {A : Type U}{x y z w : A} →
          (p : x ≡ y) →
          (q : y ≡ z) →
          (r : z ≡ w) →
          (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc refl refl refl = refl

-- inverse

!_ : {A : Type U}{x y : A} → x ≡ y → y ≡ x
! refl = refl

∙-cancel-left : {A : Type U}{x y : A}(p : x ≡ y) → p ∙ (! p) ≡ refl
∙-cancel-left refl = refl

∙-cancel-right : {A : Type U}{x y : A}(p : x ≡ y) → (! p) ∙ p ≡ refl
∙-cancel-right refl = refl

!-! : {A : Type U}{x y : A}(p : x ≡ y) → ! (! p) ≡ p
!-! refl = refl

-- equational reasoning

infix 1 begin_

begin_ : ∀ {l}{A : Type l}{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

infixr 2 _≡⟨⟩_

_≡⟨⟩_ : ∀ {l}{A : Type l}(x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infixr 2 step-≡

step-≡ : ∀ {l}{A : Type l}(x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = x≡y ∙ y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

infix 3 _∎

_∎ : ∀ {l}{A : Type l}(x : A) → x ≡ x
_∎ _ = refl
