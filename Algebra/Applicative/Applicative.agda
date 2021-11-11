module Algebra.Applicative.Applicative where

open import Basics.Level
open import Algebra.Functor.Functor
open import Algebra.Monad.Monad
open import Data.Function.Function
open import Data.Maybe.Maybe
open import Data.List.List
open import Data.Vec.Vec renaming (repeat to vec)
open import Reflection.Core


record Applicative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<*>_
  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap {{super}} : Functor F

open Applicative {{...}} public

instance
    ApplicativeMaybe : ∀ {a} → Applicative (Maybe {a})
    pure  {{ApplicativeMaybe}} = just
    _<*>_ {{ApplicativeMaybe}} mf mx = maybe nothing (λ f → fmap f mx) mf

    ApplicativeList : ∀ {l} → Applicative (List {l})
    pure  {{ApplicativeList}} x = x ∷ []
    _<*>_ {{ApplicativeList}} = monadAp (flip concatMap)

    ApplicativeVec : ∀ {a n} → Applicative {a} (flip Vec n)
    pure  {{ApplicativeVec {n = n}}} = vec n
    _<*>_ {{ApplicativeVec}} = vapp

    ApplicativeTC : ∀ {l} → Applicative {l} TC
    pure  {{ApplicativeTC}} = returnTC
    _<*>_ {{ApplicativeTC}} = monadAp bindTC
