{-# OPTIONS --sized-types #-}

module Language.Lambda.Untyped where

  open import Coinduction.Size
  open import Coinduction.DelayMonad
  open import Data.Nat.Nat
  open import Data.Maybe.Maybe renaming (map to mapM)
  open import Data.Fin.Fin

  data Term : ℕ → Set where
    var : ∀ {n} → Fin n → Term n
    _∙_ : ∀ {n} → Term n → Term n → Term n
    `λ  : ∀ {n} → Term (suc n) → Term n

  Ren : ℕ → ℕ → Set
  Ren n m = Fin n → Fin m

  weak-ren : ∀ {n m} → Ren n m → Ren (suc n) (suc m)
  weak-ren r zero = zero
  weak-ren r (suc i) = suc (r i)

  rename : ∀ {n m} → Ren n m → Term n → Term m
  rename r (var x) = var (r x)
  rename r (e ∙ e₁) = rename r e ∙ rename r e₁
  rename r (`λ e) = `λ (rename (weak-ren r) e)

  Sub : ℕ → ℕ → Set
  Sub n m = Fin n → Term m

  weak-sub : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
  weak-sub s zero = var zero
  weak-sub s (suc i) = rename suc (s i)

  substitution : ∀ {n m} → Sub n m → Term n → Term m
  substitution s (var x) = s x
  substitution s (e ∙ e₁) = substitution s e ∙ substitution s e₁
  substitution s (`λ e) = `λ (substitution (weak-sub s) e)

  [_↦_] : ∀ {n} → Term n → Term (suc n) → Term n
  [ e ↦ e' ] = substitution (λ { zero → e
                                ; (suc i) → var i})
                             e'

  step : ∀ {n : ℕ} → Term n → Maybe (Term n)
  step (var x) = nothing
  step ((`λ e) ∙ e') = just [ e' ↦ e ]
  step (e ∙ e₁) with step e
  ...| nothing = mapM (e ∙_) (step e₁)
  ...| just e' = just (e' ∙ e₁)
  step (`λ e) = mapM `λ (step e)


  ∞eval : ∀ {n i} → Term n → ∞Delay (Term n) i
  eval : ∀ {n i} → Term n → Delay (Term n) i

  eval e with step e
  ...| nothing = now e
  ...| just e' = later (∞eval e')

  ∞Delay.force (∞eval e) = eval e

  extract : ℕ → ∀ {n} → Delay (Term n) ∞ → Maybe (Term n)
  extract n (now e) = just e
  extract zero (later ∞d) = nothing
  extract (suc n) (later ∞d) = extract n (∞Delay.force ∞d)

  run : ℕ → ∀ {n} → Term n → Maybe (Term n)
  run gas e = extract gas (eval e)
