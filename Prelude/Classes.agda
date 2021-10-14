module Prelude.Classes where

open import Data.Nat.Le renaming ( _≤_       to _≤N_
                                 ; ≤-refl    to ≤N-refl
                                 ; ≤-antisym to ≤N-antisym
                                 ; ≤-trans   to ≤N-trans
                                 )
open import Data.Nat.Nat

open import Relation.Properties
open import Relation.Equality.Propositional

record Eq (A : Set) : Set₁ where
  field
    _==_    : A → A → Set
    ≡-refl  : Reflexive  _==_
    ≡-sym   : Symmetric  _==_
    ≡-trans : Transitive _==_

open Eq {{...}} public

record Ord (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : Reflexive _≤_
    ≤-antisym : AntiSymmetric _≤_
    ≤-trans   : Transitive _≤_

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

open Ord {{...}} public

variable A : Set

! : {{ x : A }} → A
! {{x}} = x

variable x y : A

data Tri {{_ : Ord A}} : A → A → Set where
  less    : {{x≤y : x ≤ y}} → Tri x y
  equal   : {{x≡y : x ≡ y}} → Tri x y
  greater : {{x≥y : x ≥ y}} → Tri x y

record Compare (A : Set) : Set₁ where
  field
    {{Ord-A}} : Ord A
    compare   : (x y : A) → Tri x y

open Compare {{...}} public


data [_]∞ (A : Set) : Set where
  -∞ : [ A ]∞
  ⟨_⟩ : A → [ A ]∞
  +∞ : [ A ]∞


module Ord-[]∞ {A : Set}{{ A-≤ : Ord A }} where

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ : ∀ {x} → -∞ ≤∞ x
    ⟨⟩-≤  : ∀ { x y : A} → x ≤ y → ⟨ x ⟩ ≤∞ ⟨ y ⟩
    +∞-≤ : ∀ {x} → x ≤∞ +∞

  []∞-refl : Reflexive _≤∞_
  []∞-refl { -∞} = -∞-≤
  []∞-refl {⟨ x ⟩} = ⟨⟩-≤ ≤-refl
  []∞-refl {+∞} = +∞-≤

  []∞-trans : Transitive _≤∞_
  []∞-trans -∞-≤      _          = -∞-≤
  []∞-trans (⟨⟩-≤ x≤y) (⟨⟩-≤ y≤z) = ⟨⟩-≤ (≤-trans x≤y y≤z)
  []∞-trans _          +∞-≤      = +∞-≤

  []∞-antisym : AntiSymmetric _≤∞_
  []∞-antisym -∞-≤ -∞-≤ = refl
  []∞-antisym (⟨⟩-≤ x≤y) (⟨⟩-≤ y≤z) = cong ⟨_⟩ (≤-antisym x≤y y≤z)
  []∞-antisym +∞-≤ +∞-≤ = refl


  instance
    Ord-[]∞ : {{_ : Ord A}} → Ord [ A ]∞
    _≤_       {{Ord-[]∞}} = _≤∞_
    ≤-refl    {{Ord-[]∞}} = []∞-refl
    ≤-trans   {{Ord-[]∞}} = []∞-trans
    ≤-antisym {{Ord-[]∞}} = []∞-antisym

open Ord-[]∞ public


module Lemmas {{ _ : Ord A }} where

  instance
    -∞-≤-any : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-any = -∞-≤

    +∞-≤-any : {y : [ A ]∞} → y ≤ +∞
    +∞-≤-any = +∞-≤

    ⟨⟩-≤-≤ : {x y : A} {{x≤y : x ≤ y}} → ⟨ x ⟩ ≤ ⟨ y ⟩
    ⟨⟩-≤-≤ {{x≤y = x≤y}} = ⟨⟩-≤ x≤y

open Lemmas public
