module Algebra.Alternative.Alternative where

open import Basics.Level
open import Algebra.Functor.Functor
open import Data.List.List
open import Data.Maybe.Maybe
open import Reflection.Core

module _ {a b}(F : Set a → Set b) where
  record FunctorZero : Set (lsuc a ⊔ b) where
    field
      empty : ∀ {A} → F A
      overlap {{super}} : Functor F

  record Alternative : Set (lsuc a ⊔ b) where
    infixl 3 _<|>_
    field
      _<|>_ : ∀ {A} → F A → F A → F A
      overlap {{super}} : FunctorZero

open FunctorZero {{...}} public

open Alternative {{...}} public

instance
  FunctorZeroMaybe : ∀ {a} → FunctorZero (Maybe {a})
  empty {{FunctorZeroMaybe}} = nothing

  -- Left-biased choice
  AlternativeMaybe : ∀ {a} → Alternative (Maybe {a})
  _<|>_ {{AlternativeMaybe}} nothing y = y
  _<|>_ {{AlternativeMaybe}} x       y = x

  FunctorZeroList : ∀ {a} → FunctorZero (List {a})
  empty {{FunctorZeroList}} = []

  AlternativeList : ∀ {a} → Alternative (List {a})
  _<|>_ {{AlternativeList}} = _++_

  FunctorZeroTC : ∀ {l} → FunctorZero {l} TC
  empty {{FunctorZeroTC}} = typeError []

  AlternativeTC : ∀ {l} → Alternative {l} TC
  _<|>_ {{AlternativeTC}} = catchTC
