module Data.Generic.SampleReps where

open import Data.Generic.Regular

module NAT where

  natF : ∀ {n} → Reg n
  natF = `μ (`1 `+ `zero)


  nat : ∀ {n}(Γ : Ctx n) → Set
  nat Γ = Data Γ natF

  pattern z = rec (inl unit)
  pattern s n = rec (inr (top n))


  plus : ∀ {n}{Γ : Ctx n} → nat Γ → nat Γ → nat Γ
  plus z m = m
  plus (s n) m = s (plus n m)

module LIST where

  open import Data.Nat.Nat

  listF : ∀ {n} → Reg (suc n)
  listF = `μ (`1 `+ (`wk `zero `* `zero))

  list : ∀ {n} → Ctx (suc n) → Set
  list Γ = Data Γ listF

  pattern nil = rec (inl unit)
  pattern cons x xs = rec (inr (pair (pop x) (top xs)))

  append : ∀ {n}{Γ : Ctx (suc n)} → list Γ → list Γ → list Γ
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
