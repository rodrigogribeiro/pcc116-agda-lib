{-# OPTIONS --copatterns --sized-types --guardedness  #-}

open import Coinduction.Size
open import Data.Nat.Nat
open import Relation.Equality.Propositional

module Coinduction.Stream where

  record Stream (i : Size)(A : Set) : Set where
    constructor _∷_
    coinductive
    field
      head : A
      tail : {j : Size< i} → Stream j A

  open Stream

  zeros : ∀ {i} → Stream i ℕ
  head zeros = 0
  tail zeros = zeros


  interleave : ∀ {i A} → Stream i A → Stream i A → Stream i A
  head (interleave s1 s2) = head s1
  tail (interleave s1 s2) = interleave s2 (tail s1)


  map : ∀ {A B i} → (A → B) → Stream i A → Stream i B
  head (map f xs) = f (head xs)
  tail (map f xs) = map f (tail xs)

  zipWith : ∀ {A B C i} → (A → B → C) →
                           Stream i A    →
                           Stream i B    →
                           Stream i C
  head (zipWith f xs ys) = f (head xs) (head ys)
  tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

  ones : ∀ {i} → Stream i ℕ
  head ones = 1
  tail ones = ones

  record _∼_ {A : Set} (s s' : Stream ∞ A) : Set where
    coinductive
    field
      head : head s ≡ head s'
      tail : tail s ∼ tail s'

  open _∼_

  ones-mapsuc : ones ∼ map suc zeros
  head ones-mapsuc = refl
  tail ones-mapsuc = ones-mapsuc

  enum : ∀ {i} → ℕ → Stream i ℕ
  head (enum n) = n
  tail (enum n) = enum (suc n)

  nats : ∀ {i} → Stream i ℕ
  nats = enum 0

  data _∈_ {A}(x : A)(xs : Stream ∞ A) : Set where
    here  : x ≡ head xs → x ∈ xs
    there : x ∈ tail xs → x ∈ xs

  ∈-suc : ∀ {n m : ℕ} → n ∈ enum m → suc n ∈ enum (suc m)
  ∈-suc (here refl) = here refl
  ∈-suc (there n∈enumm) = there (∈-suc n∈enumm)

  ℕ∈nats : ∀ (n : ℕ) → n ∈ nats
  ℕ∈nats zero = here refl
  ℕ∈nats (suc n) = there (∈-suc (ℕ∈nats n))
