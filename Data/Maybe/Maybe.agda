module Data.Maybe.Maybe where


data Maybe {a}(A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

{-# BUILTIN MAYBE  Maybe #-}


maybe : ∀ {a b}{A : Set a}{B : Set b} → B → (A → B) → Maybe A → B
maybe v f nothing  = v
maybe v f (just x) = f x


map :  ∀ {a b}{A : Set a}{B : Set b} → (A → B) → Maybe A → Maybe B
map _ nothing  = nothing
map f (just x) = just (f x)

infixl 1 _>>=_ _>>_

_>>=_ : ∀ {a b}{A : Set a}{B : Set b} → Maybe A → (A → Maybe B) → Maybe B
nothing  >>= _ = nothing
(just x) >>= f = f x

_>>_ : ∀ {a b}{A : Set a}{B : Set b} → Maybe A → Maybe B → Maybe B
_ >> m = m
