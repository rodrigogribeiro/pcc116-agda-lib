module Data.Generic.GEq where

  open import Data.Empty.Empty
  open import Data.Function.Function
  open import Data.Generic.Regular
  open import Data.Nat.Nat
  open import Data.Product.Product

  open import Data.Function.Function

  open import Relation.Decidable.Dec
  open import Relation.Equality.Propositional

  top-inv : ∀ {n}{t : Reg n}{Γ : Ctx n}{x y : Data Γ t} →
              top x ≡ top y → x ≡ y
  top-inv refl = refl

  pop-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ t} →
              pop {s = s} x ≡ pop {s = s} y → x ≡ y
  pop-inv refl = refl

  def-inv : ∀ {n}{s : Reg n}{t : Reg (suc n)}{Γ : Ctx n}
              {x y : Data (Γ , s) t} → def x ≡ def y → x ≡ y
  def-inv refl = refl

  inl-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ s}
              → inl {t = t} x ≡ inl {t = t} y → x ≡ y
  inl-inv refl = refl

  inr-inv : ∀ {n}{s t : Reg n}{Γ : Ctx n}{x y : Data Γ t}
              → inr {s = s} x ≡ inr {s = s} y → x ≡ y
  inr-inv refl = refl

  pair-inv : ∀ {n}{Γ : Ctx n}{S T : Reg n}
               {x x' : Data Γ S}{y y' : Data Γ T} →
               pair x y ≡ pair x' y' → x ≡ x' × y ≡ y'
  pair-inv refl = refl , refl

  rec-inv : ∀ {n}{Γ : Ctx n}{F : Reg (suc n)}
              {x y : Data (Γ , `μ F) F} →
              rec x ≡ rec y → x ≡ y
  rec-inv refl = refl

  decEq : ∀ {n}{Γ : Ctx n}{t : Reg n}(x y : Data Γ t) → Dec (x ≡ y)
  decEq (top x) (top y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ top-inv)
  decEq (pop x) (pop y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ pop-inv)
  decEq (def x) (def y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ def-inv)
  decEq (inl x) (inl y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ inl-inv)
  decEq (inl x) (inr y) = no (λ ())
  decEq (inr x) (inl y) = no (λ ())
  decEq (inr x) (inr y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ inr-inv)
  decEq unit unit = yes refl
  decEq (pair x x₁) (pair y y₁) with decEq x y | decEq x₁ y₁
  ...| yes eq  | yes eq' rewrite eq | eq' = yes refl
  ...| no  neq | _  = no (neq ∘ proj₁ ∘ pair-inv)
  ...| _       | no neq' = no (neq' ∘ proj₂ ∘ pair-inv)
  decEq (rec x) (rec y) with decEq x y
  ...| yes eq rewrite eq = yes refl
  ...| no neq = no (neq ∘ rec-inv)
