module Algebra.Functor.Functor where

open import Basics.Level
open import Data.Function.Function
open import Data.Maybe.Maybe
open import Data.List.List renaming (map to mapL)
open import Data.Vec.Vec renaming (map to vmap)
open import Reflection.Core


record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

mapTC : ∀ {l}{A B : Set l} → (A → B) → TC A → TC B
mapTC f m = bindTC m λ x → returnTC (f x)

instance
  FunctorMaybe : ∀ {a} → Functor (Maybe {a})
  fmap {{FunctorMaybe}} f m = maybe nothing (just ∘ f) m

  FunctorList : ∀ {l} → Functor (List {l})
  fmap {{FunctorList}} = mapL

  FunctorVec : ∀ {a n} → Functor {a} (flip Vec n)
  fmap {{FunctorVec}} = vmap

  FunctorTC : ∀ {l} → Functor {l} TC
  fmap {{FunctorTC}} = mapTC
