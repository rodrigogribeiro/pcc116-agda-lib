module Algebra.Traversable.Traversable where

open import Basics.Level
open import Algebra.Functor.Functor
open import Algebra.Applicative.Applicative

open import Data.List.List renaming (foldr to foldrL)
open import Data.Maybe.Maybe
open import Data.Vec.Vec

record Traversable {a} (T : Set a → Set a) : Set (lsuc a) where
  field
    traverse : ∀ {F : Set a → Set a} {A B}
                 {{AppF : Applicative F}} →
                 (A → F B) → T A → F (T B)
    overlap {{super}} : Functor T

open Traversable {{...}} public

instance
  TraversableMaybe : ∀ {a} → Traversable {a} Maybe
  traverse {{TraversableMaybe}} f m = maybe (pure nothing) (λ x -> pure just <*> f x) m

  TraversableList : ∀ {a} → Traversable {a} List
  traverse {{TraversableList}} f xs = foldrL (λ x fxs → pure _∷_ <*> f x <*> fxs) (pure []) xs

  TraversableVec : ∀ {a n} → Traversable {a} (λ A → Vec A n)
  traverse {{TraversableVec}} f []       = pure []
  traverse {{TraversableVec}} f (x ∷ xs) = ⦇ f x ∷ traverse f xs ⦈
