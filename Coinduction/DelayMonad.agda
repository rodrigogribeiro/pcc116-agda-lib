{-# OPTIONS --sized-types #-}

module Coinduction.DelayMonad where

  open import Coinduction.Size
  open import Algebra.Monad.Monad

  data Delay (i : Size)(A : Set)  : Set

  record ∞Delay (i : Size)(A : Set) : Set where
    coinductive
    constructor ⟨_⟩
    field
      force : {j : Size< i} → Delay j A

  open ∞Delay public

  data Delay i A where
    now   : A → Delay i A
    later : ∞Delay i A → Delay i A

  map : ∀ {A B i} → (A → B) → Delay i A → Delay i B
  ∞map : ∀ {A B i} → (A → B) → ∞Delay i A → ∞Delay i B

  force (∞map f d) = map f (force d)

  map f (now x) = now (f x)
  map f (later c) = later (∞map f c)

  join : ∀ {A i} → Delay i (Delay i A) → Delay i A

  ∞join : ∀ {A i} → ∞Delay i (Delay i A) → ∞Delay i A
  force (∞join d) = join (force d)

  join (now d) = d
  join (later x) = later (∞join x)

  instance
    monadDelay : ∀ {i} → Monad (Delay i)
    monadDelay = record { return = now ; _>>=_ = λ m f → join (map f m) }
