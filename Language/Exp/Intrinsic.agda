open import Basics.Admit
open import Data.Bool.Bool
open import Data.Nat.Nat


module Language.Exp.Intrinsic where

open import Language.Exp.Extrinsic

⟦_⟧T : Type → Set
⟦ nat ⟧T  = ℕ
⟦ bool ⟧T = Bool

data TExp : Type → Set where
  val  : ∀ {t} → ⟦ t ⟧T → TExp t
  _⊕_  : TExp nat → TExp nat → TExp nat
  _<_  : TExp nat → TExp nat → TExp bool
  cond : ∀ {t} → TExp bool → TExp t → TExp t → TExp t


eval : ∀ {t} → TExp t → ⟦ t ⟧T
eval (val x) = x
eval (e ⊕ e₁) = eval e + eval e₁
eval (e < e₁) = eval e <? eval e₁
eval (cond e e₁ e₂) = if eval e then eval e₁ else eval e₂

-- exercise: define erase from typed expressions to untyped ones

erase : ∀ {t} → TExp t → Exp
erase = admit

-- exercise: define the elaboration between untyped and typed expressions

data Elab : Exp → Set where
  ok : ∀ {t}(e : TExp t) → Elab (erase e)
  bad : {e : Exp} → Elab e

elaborate : (e : Exp) → Elab e
elaborate = admit
