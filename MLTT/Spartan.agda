{-# OPTIONS --without-K --exact-split #-}

module MLTT.Spartan where

open import MLTT.Universes

variable U V W T : Universe

module Unit where
-- unit type

  data 𝟙 : Type U₀ where
    ⋆ : 𝟙


  -- induction principle

  𝟙-induction : (P : 𝟙 → Type U) → P ⋆ → (x : 𝟙) → P x
  𝟙-induction P p ⋆ = p

  -- recursion principle

  𝟙-recursion : (B : Type U) → B → 𝟙 → B
  𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

  -- terminal object

  !𝟙′ : (A : Type U) → A → 𝟙
  !𝟙′ A x = ⋆

  !𝟙 : {A : Type U} → A → 𝟙
  !𝟙 x = ⋆

module Empty where

  data 𝟘 : Type U₀ where

  -- induction principle

  𝟘-induction : (A : 𝟘 → Type U) → (x : 𝟘) → A x
  𝟘-induction A ()

  -- recursion principle

  𝟘-recursion : (A : Type U) → 𝟘 → A
  𝟘-recursion A a = 𝟘-induction (λ _ → A) a

  !𝟘 : (A : Type U) → 𝟘 → A
  !𝟘 = 𝟘-recursion

  -- negation definition

  is-empty : Type U → Type U
  is-empty A = A → 𝟘

  ¬_ : Type U → Type U
  ¬ A = A → 𝟘

module Natural where

  data ℕ : Type U₀ where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}

  -- induction principle

  ℕ-induction : (P : ℕ → Type U) →
                P 0               →
                ((n : ℕ) → P n → P (suc n)) →
                (n : ℕ) → P n
  ℕ-induction P base IH zero = base
  ℕ-induction P base IH (suc n) = IH n (ℕ-induction P base IH n)


  -- recursion principle

  ℕ-recursion : (A : Type U)  →
                A             →
                (ℕ → A → A) →
                ℕ             →
                A
  ℕ-recursion A = ℕ-induction (λ _ → A)

  -- iteration

  ℕ-iteration : (A : Type U) →
                A            →
                (A → A)     →
                ℕ            →
                A
  ℕ-iteration A a f = ℕ-recursion A a (λ _ y →  f y)


-- ordering on ℕ

module ℕ-order where
  open Unit
  open Empty
  open Natural

  _≤_ : ℕ → ℕ → Type U₀
  0     ≤ y     = 𝟙
  suc _ ≤ zero  = 𝟘
  suc x ≤ suc y = x ≤ y

  _≥_ : ℕ → ℕ → Type U₀
  x ≥ y = y ≤ x


-- disjoint union: sum types

module Sum where

  infixl 4 _+_

  data _+_ (A : Type U)(B : Type V)  :  Type (U ⊔ V) where
    inl : A → A + B
    inr : B → A + B

  -- induction principle

  +-induction : {A : Type U}{B : Type V}(P : A + B → Type W) →
                ((a : A) → P (inl a))                        →
                ((b : B) → P (inr b))                        →
                (z : A + B) → P z
  +-induction P f g (inl a) = f a
  +-induction P f g (inr b) = g b

  -- recursion

  +-recursion : {A : Type U}{B : Type V}{C : Type W} →
                (A → C)                             →
                (B → C)                             →
                (A + B) → C
  +-recursion {C = C} = +-induction (λ _ → C)


-- two point type: booleans

module Two where

  open Sum
  open Unit

  𝟚 : Type U₀
  𝟚 = 𝟙 + 𝟙

  -- definition of constants

  pattern false = inl ⋆
  pattern true  = inr ⋆

  -- induction

  𝟚-induction : (P : 𝟚 → Type U) → P false → P true → (n : 𝟚) → P n
  𝟚-induction P Pfalse Ptrue false = Pfalse
  𝟚-induction P Pfalse Ptrue true  = Ptrue

-- Dependent products: Σ types

module Sigma where


  record Σ {A : Type U}(B : A → Type V) : Type (U ⊔ V) where
    constructor _,_
    field
      fst : A
      snd : B fst

  -- induction principle

  Σ-induction : {A : Type U}{B : A → Type V}{P : Σ B → Type W} →
                ((a : A) → (b : B a) → P (a , b))                →
                ((a , b) : Σ B)     → P (a , b)
  Σ-induction g (a , b) = g a b


  -- cartesian product

  _×_ : Type U → Type V → Type (U ⊔ V)
  A × B = Σ {A = A} (λ _ → B)


-- pi types

module Pi where


Π : {A : Type U}(B : A → Type V) → Type (U ⊔ V)
Π {A = A} B = (x : A) → B x

_∘_ : {A : Type U}{B : Type V}{C : B → Type W} →
      ((b : B) → C b)                          →
      (f : A → B)                              →
      (a : A) → C (f a)
g ∘ f = λ a → g (f a)


-- identity type

module Identity where

  data Id {U}(A : Type U) : A → A → Type U where
    refl : (x : A) → Id A x x

  infix 4 _≡_

  _≡_ : {A : Type U} → A → A → Type U
  x ≡ y = Id _ x y

  -- induction

  𝕁 : (A : Type U)(P : (x y : A) → x ≡ y → Type V) →
      ((x : A) → P x x (refl x))                    →
      (x y : A)(p : x ≡ y) → P x y p
  𝕁 A P f x x (refl x) = f x

  -- equality transport

  transport : {A : Type U}(P : A → Type V){x y : A} →
              x ≡ y → P x → P y
  transport P (refl x) px = px

  -- composition of identifications

  lhs : {A : Type U}{x y : A} → x ≡ y → A
  lhs {x = x} _ = x

  rhs : {A : Type U}{x y : A} → x ≡ y → A
  rhs {y = y} _ = y

  _∙_ : {A : Type U}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  xy ∙ yz = transport (lhs xy ≡_) yz xy

  -- mixfix operators for identity type

  _≡⟨_⟩_ : {A : Type U}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ xy ⟩ yz = xy ∙ yz

  _∎ : {A : Type U}(x : A) → x ≡ x
  x ∎ = refl x

  _⁻¹ : {A : Type U}{x y : A} → x ≡ y → y ≡ x
  xy ⁻¹ = transport (_≡ lhs xy) xy (refl (lhs xy))

  -- congruence

  ap : {A : Type U}{B : Type V}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
  ap f {x}{y} xy = transport (λ _ → f x ≡ f _) xy (refl (f x))

  -- pointwise equality of functions

  _~_ : {A : Type U}{B : A → Type V} → Π B → Π B → Type (U ⊔ V)
  f ~ g = (x : _) → f x ≡ g x

  -- negation

  open Empty

  ¬¬ : Type U → Type U
  ¬¬ A = ¬ (¬ A)

  ¬¬¬ : Type U → Type U
  ¬¬¬ A = ¬ (¬ (¬ A))

  -- double negation validity

  dni : (A : Type U) → A → ¬¬ A
  dni A a u = u a

  -- contrapositiva

  contrapositive : {A : Type U}{B : Type V} → (A → B) → (¬ B → ¬ A)
  contrapositive f nb a = nb (f a)

  -- definition of logical equivalence

  open Sigma

  infix 4 _⇔_

  _⇔_ : Type U → Type V → Type (U ⊔ V)
  A ⇔ B = (A → B) × (B → A)


  -- absurdity equivalence

  absurdity³-absurdity : {A : Type U} → ¬¬¬ A ⇔ ¬ A
  absurdity³-absurdity {A = A} = first , second
    where
      first : (¬¬¬ A) → ¬ A
      first = contrapositive (dni A)

      second : ¬ A → ¬¬¬ A
      second = dni (¬ A)

  -- inequality

  _≢_ : {A : Type U} → A → A → Type U
  x ≢ y = ¬ (x ≡ y)

  ≢-sym : {A : Type U}{x y : A} → x ≢ y → y ≢ x
  ≢-sym {x = x}{y = y} x≢y = λ (p : y ≡ x) → x≢y (p ⁻¹)

  Id→Fun : {A B : Type U}→ A ≡ B → A → B
  Id→Fun (refl A) = λ (x : A) → x

  -- a simple property

  open Unit
  open Empty
  open Two

  𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
  𝟙-is-not-𝟘 p = Id→Fun p ⋆

  true-is-not-false : true ≢ false
  true-is-not-false p = 𝟙-is-not-𝟘 q
    where
      f : 𝟚 → Type U₀
      f false = 𝟘
      f true  = 𝟙

      q :  𝟙 ≡ 𝟘
      q = ap f p

  -- decidable equality

  open Sum

  Dec : Type U → Type U
  Dec A = A + ¬ A

  EqDec : Type U → Type U
  EqDec A = (x y : A) → Dec (x ≡ y)

  -- two points type has a decidable equality

  𝟚-EqDec : EqDec 𝟚
  𝟚-EqDec false false = inl (refl (inl ⋆))
  𝟚-EqDec false true  = inr (≢-sym true-is-not-false)
  𝟚-EqDec true  false = inr true-is-not-false
  𝟚-EqDec true  true  = inl (refl (inr ⋆))

  -- not false is true

  not-false-is-true : (n : 𝟚) → n ≢ false → n ≡ true
  not-false-is-true false f = !𝟘 (false ≡ true) (f (refl false))
  not-false-is-true true  f = refl true


module Peano where

  open Unit
  open Empty
  open Natural
  open Sigma
  open Sum
  open Identity
  open ℕ-order

  suc-not-zero : (n : ℕ) → suc n ≢ 0
  suc-not-zero n p = 𝟙-is-not-𝟘 (g p)
    where
      f : ℕ → Type U₀
      f zero    = 𝟘
      f (suc _) = 𝟙

      g : suc n ≡ 0 → 𝟙 ≡ 𝟘
      g = ap f


  pred : ℕ → ℕ
  pred 0       = 0
  pred (suc x) = x

  suc-inv : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  suc-inv = ap pred

  ℕ-EqDec : EqDec ℕ
  ℕ-EqDec zero zero = inl (refl zero)
  ℕ-EqDec zero (suc y) = inr (≢-sym (suc-not-zero y))
  ℕ-EqDec (suc x) zero = inr (suc-not-zero x)
  ℕ-EqDec (suc x) (suc y) = f (ℕ-EqDec x y)
    where
      f : Dec (x ≡ y) → Dec (suc x ≡ suc y)
      f (inl p) = inl (ap suc p)
      f (inr q) = inr (q ∘ suc-inv)

  -- Exercises

  postulate admit : {A : Type U} → A

  _⊕_  _⊗_ : ℕ → ℕ → ℕ

  x ⊕ 0     = x
  x ⊕ suc y = suc (x ⊕ y)

  x ⊗ 0     = 0
  x ⊗ suc y = x ⊕ x ⊗ y

  infixl 20 _⊕_
  infixl 21 _⊗_

  -- Exercise 1.

  +-assoc : (x y z : ℕ) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  +-assoc x y z = admit

  +-comm : (x y : ℕ) → x ⊕ y ≡ y ⊕ x
  +-comm = admit

  -- Exercise 2.

  _≼_ : ℕ → ℕ → Type U₀
  n ≼ m  = Σ (λ (z : ℕ) → n ⊕ z ≡ m)

  ≤-gives-≼ : (x y : ℕ) → x ≤ y → x ≼ y
  ≤-gives-≼ = admit

  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y
  ≼-gives-≤ = admit

  -- Exercise 3.

  _<_ : ℕ → ℕ → Type U₀
  x < y = suc x ≤ y

  bounded-induction : (P : ℕ → Type U)(k : ℕ)  →
                      P k                       →
                      ((n : ℕ) → n < k → P n) →
                      (n : ℕ) → n < suc k → P n
  bounded-induction = admit
