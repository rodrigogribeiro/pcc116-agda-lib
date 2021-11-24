module Relation.Induction.Natural where

open import Data.Nat.Nat
open import Data.Nat.Div.NonZero
open import Relation.Induction.WellFounded

data _<_ (n : ℕ) : ℕ → Set where
  <-base : n < suc n
  <-step : ∀ {m} → n < m → n < suc m

<-suc : ∀ {n m} → n < m → suc n < suc m
<-suc <-base = <-base
<-suc (<-step p) = <-step (<-suc p)

0<sucn : ∀ {n} → 0 < suc n
0<sucn {zero} = <-base
0<sucn {suc n} = <-step 0<sucn

<-ℕ-wf : WellFounded _<_
<-ℕ-wf x = acc (IH x)
  where
    IH : ∀ x y → y < x → Acc _<_ y
    IH (suc x) .x <-base = <-ℕ-wf x
    IH (suc x) y (<-step y<x) = IH x y y<x

n-m<n+1 : ∀ (n m : ℕ){{_ : NonZero m}} → (n - m) < suc n
n-m<n+1 zero    (suc m)       = <-base
n-m<n+1 (suc n) (suc zero)    = <-step <-base
n-m<n+1 (suc n) (suc (suc m)) = <-step (n-m<n+1 n (suc m))
