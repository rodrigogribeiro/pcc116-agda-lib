module Data.Generic.Regular where

open import Data.Nat.Nat

-- universe definition

infixr 4 _`+_
infixr 5 _`*_

data Reg : ℕ → Set where
  `zero : ∀ {n} → Reg (suc n)
  `wk : ∀ {n}(r : Reg n) → Reg (suc n)
  `let : ∀ {n}(s : Reg n)(t : Reg (suc n)) → Reg n
  `0 : ∀ {n} → Reg n
  `1 : ∀ {n} → Reg n
  _`+_ : ∀ {n}(s t : Reg n) → Reg n
  _`*_ : ∀ {n}(s t : Reg n) → Reg n
  `μ : ∀ {n}(f : Reg (suc n)) → Reg n


-- data syntax

data Ctx : ℕ → Set where
  [] : Ctx 0
  _,_ : ∀ {n} → Ctx n → Reg n → Ctx (suc n)

data Data : ∀ {n} → Ctx n → Reg n → Set where
  top : ∀ {n}{t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data (Γ , t) `zero
  pop : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data (Γ , s) (`wk t)
  def : ∀ {n}{t : Reg (suc n)}{s : Reg n}{Γ : Ctx n}
             (e : Data (Γ , s) t) → Data Γ (`let s t)
  inl : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ s) → Data Γ (s `+ t)
  inr : ∀ {n}{s t : Reg n}{Γ : Ctx n}(e : Data Γ t) → Data Γ (s `+ t)
  unit : ∀ {n}{Γ : Ctx n} → Data Γ `1
  pair : ∀ {n}{S T : Reg n}{Γ : Ctx n}
              (s : Data Γ S)
              (t : Data Γ T) →
              Data Γ (S `* T)
  rec : ∀ {n}{F : Reg (suc n)}{Γ : Ctx n}
             (x : Data (Γ , `μ F) F) → Data Γ (`μ F)
