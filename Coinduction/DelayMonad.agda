{-# OPTIONS --sized-types #-}

module Coinduction.DelayMonad where

  open import Coinduction.Size


  data Delay (A : Set)(i : Size) : Set

  record ∞Delay (A : Set)(i : Size) : Set where
    coinductive
    constructor ⟨_⟩
    field
      force : {j : Size< i} → Delay A j

  open ∞Delay public

  data Delay A i where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  map : ∀ {A B i} → (A → B) → Delay A i → Delay B i
  ∞map : ∀ {A B i} → (A → B) → ∞Delay A i → ∞Delay B i

  force (∞map f d) = map f (force d)

  map f (now x) = now (f x)
  map f (later c) = later (∞map f c)

  join : ∀ {A i} → Delay (Delay A i) i → Delay A i

  ∞join : ∀ {A i} → ∞Delay (Delay A i) i → ∞Delay A i
  force (∞join d) = join (force d)

  join (now d) = d
  join (later x) = later (∞join x)

  _>>=_ : ∀ {A B i} → Delay A i → (A → Delay B i) → Delay B i
  m >>= f = join (map f m)
