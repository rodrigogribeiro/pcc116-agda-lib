{-# OPTIONS --sized-types #-}

module Language.Lambda.Typed where
  open import Algebra.Monad.Monad
  open import Coinduction.Size
  open import Data.Empty.Empty
  open import Data.Function.Function hiding (id)
  open import Data.List.List hiding (map)
  open import Data.List.Relation.Any
  open import Data.Nat.Nat
  open import Data.Product.Product
  open import Data.Unit.Unit
  open import Relation.Decidable.Dec
  open import Relation.Equality.Propositional


  data Ty : Set where
    ι    : Ty
    _⇒_ : Ty → Ty → Ty

  ⇒-inv : ∀ {t₁ t₂ t₁' t₂'} →
             (t₁ ⇒ t₂) ≡ (t₁' ⇒ t₂') →
             t₁ ≡ t₁' × t₂ ≡ t₂'
  ⇒-inv refl = refl , refl

  _≟Ty_ : ∀ (t t' : Ty) → Dec (t ≡ t')
  ι ≟Ty ι = yes refl
  ι ≟Ty (t' ⇒ t'') = no (λ ())
  (t ⇒ t₁) ≟Ty ι = no (λ ())
  (t ⇒ t₁) ≟Ty (t' ⇒ t'') with t ≟Ty t' | t₁ ≟Ty t''
  ...| yes eq | yes eq' rewrite eq | eq' = yes refl
  ...| yes eq | no  eq' rewrite eq = no (eq' ∘ proj₂ ∘ ⇒-inv)
  ...| no  eq | _ = no (eq ∘ proj₁ ∘ ⇒-inv)


  Ctx : Set
  Ctx = List Ty


  infix 0 _⊢_

  data _⊢_ : Ctx → Ty → Set where
    var : ∀ {Γ t} → t ∈ Γ → Γ ⊢ t
    `λ  : ∀ {Γ t t'} → t ∷ Γ ⊢ t' → Γ ⊢ t ⇒ t'
    _∙_ : ∀ {Γ t t'} → Γ ⊢ t ⇒ t' → Γ ⊢ t → Γ ⊢ t'



  ⟦_⟧T : Ty → Set
  ⟦ ι ⟧T = ⊤
  ⟦ t ⇒ t' ⟧T = ⟦ t ⟧T → ⟦ t' ⟧T


  ⟦_⟧C : Ctx → Set
  ⟦ [] ⟧C    = ⊤
  ⟦ t ∷ Γ ⟧C = ⟦ t ⟧T × ⟦ Γ ⟧C


  ⟦_⟧V : ∀ {t Γ} → t ∈ Γ → ⟦ Γ ⟧C → ⟦ t ⟧T
  ⟦ here eq ⟧V env rewrite eq = proj₁ env
  ⟦ there v ⟧V env = ⟦ v ⟧V (proj₂ env)


  ⟦_⟧ : ∀ {Γ t} → Γ ⊢ t → ⟦ Γ ⟧C → ⟦ t ⟧T
  ⟦ var x ⟧ env = ⟦ x ⟧V env
  ⟦ `λ e ⟧ env = λ val → ⟦ e ⟧ (val , env)
  ⟦ e ∙ e' ⟧ env = ⟦ e ⟧ env (⟦ e' ⟧ env)


  open import Coinduction.DelayMonad

  data Neutral (Ξ : Ctx → Ty → Set)(Γ : Ctx) : Ty → Set where
    var : ∀ {t} → t ∈ Γ → Neutral Ξ Γ t
    _∙_ : ∀ {t t'} → Neutral Ξ Γ (t' ⇒ t) → Ξ Γ t' → Neutral Ξ Γ t


  data Env (Δ : Ctx) : (Γ : Ctx) → Set

  data Value (Δ : Ctx) : (t : Ty) → Set where
    neutral : ∀ {t} → Neutral Value Δ t → Value Δ t
    `λ      : ∀ {Γ t t'}(e : (t' ∷ Γ) ⊢ t)(ρ : Env Δ Γ) → Value Δ (t' ⇒ t)

  data Env Δ where
    []   : Env Δ []
    _∷_  : ∀ {Γ t}(v : Value Δ t)(ρ : Env Δ Γ)  → Env Δ (t ∷ Γ)


  lookup : ∀ {t Δ Γ} → t ∈ Γ → Env Δ Γ → Value Δ t
  lookup (here refl) (v ∷ ρ) = v
  lookup (there t∈Γ) (v ∷ ρ) = lookup t∈Γ ρ

  eval  : ∀ {i Γ Δ t} → Γ ⊢ t → Env Δ Γ → Delay i (Value Δ t)
  apply : ∀ {i Δ t t'} → Value Δ (t' ⇒ t) → Value Δ t' → Delay i (Value Δ t)
  beta  : ∀ {i Γ Δ t t'} → (t' ∷ Γ) ⊢ t → Env Δ Γ → Value Δ t' → ∞Delay i (Value Δ t)

  eval (var v)  ρ = now (lookup v ρ)
  eval (`λ e)   ρ = now (`λ e ρ)
  eval (e ∙ e') ρ
    = do
         f ← eval e ρ
         v ← eval e' ρ
         apply f v

  apply (neutral n) v = now (neutral (n ∙ v))
  apply (`λ n ρ) v    = later (beta n ρ v)

  force (beta n ρ v)  = eval n (v ∷ ρ)


  data Normal (Γ : Ctx) : Ty → Set where
    `λ : ∀ {t t'}(n : Normal (t' ∷ Γ) t) → Normal Γ (t' ⇒ t)
    neutral : (Neutral Normal Γ ι) → Normal Γ ι


  data _⊇_ : (Γ Δ : Ctx) → Set where
    id   : ∀ {Γ} → Γ ⊇ Γ
    weak : ∀ {Γ Δ t} → Γ ⊇ Δ → (t ∷ Γ) ⊇ Δ
    lift : ∀ {Γ Δ t} → Γ ⊇ Δ → (t ∷ Γ) ⊇ (t ∷ Δ)


  _⊚_ : ∀ {Γ Δ Δ'} → Γ ⊇ Δ → Δ ⊇ Δ' → Γ ⊇ Δ'
  id ⊚ d' = d'
  weak d ⊚ d' = weak (d ⊚ d')
  lift d ⊚ id = lift d
  lift d ⊚ weak d' = weak (d ⊚ d')
  lift d ⊚ lift d' = lift (d ⊚ d')

  weaken-var : ∀ {t Γ Δ} → Γ ⊇ Δ → t ∈ Δ → t ∈ Γ
  weaken-var id t∈Δ = t∈Δ
  weaken-var (weak Γ⊇Δ) t∈Δ = there (weaken-var Γ⊇Δ t∈Δ)
  weaken-var (lift Γ⊇Δ) (here refl) = here refl
  weaken-var (lift Γ⊇Δ) (there t∈Δ) = there (weaken-var Γ⊇Δ t∈Δ)

  weaken-Value : ∀ {t Γ Δ} → Γ ⊇ Δ → Value Δ t → Value Γ t
  weaken-Neutral : ∀ {t Γ Δ} → Γ ⊇ Δ → Neutral Value Δ t → Neutral Value Γ t
  weaken-Env : ∀ {Γ Δ E} → Γ ⊇ Δ → Env Δ E → Env Γ E

  weaken-Value id v = v
  weaken-Value (weak Γ⊇Δ) (neutral x) = neutral (weaken-Neutral (weak Γ⊇Δ) x)
  weaken-Value (weak Γ⊇Δ) (`λ e ρ) = `λ e (weaken-Env (weak Γ⊇Δ) ρ)
  weaken-Value (lift Γ⊇Δ) (neutral x) = neutral (weaken-Neutral (lift Γ⊇Δ) x)
  weaken-Value (lift Γ⊇Δ) (`λ e ρ) = `λ e (weaken-Env (lift Γ⊇Δ) ρ)

  weaken-Neutral id n = n
  weaken-Neutral (weak Γ⊇Δ) (var x) = var (there (weaken-var Γ⊇Δ x))
  weaken-Neutral (weak Γ⊇Δ) (n ∙ x) = weaken-Neutral (weak Γ⊇Δ) n ∙ weaken-Value (weak Γ⊇Δ) x
  weaken-Neutral (lift Γ⊇Δ) (var x) = var (weaken-var (lift Γ⊇Δ) x)
  weaken-Neutral (lift Γ⊇Δ) (n ∙ x) = weaken-Neutral (lift Γ⊇Δ) n ∙ weaken-Value (lift Γ⊇Δ) x

  weaken-Env Γ⊇Δ [] = []
  weaken-Env Γ⊇Δ (v ∷ ρ) = weaken-Value Γ⊇Δ v ∷ weaken-Env Γ⊇Δ ρ


  wk : ∀ {t Γ} → (t ∷ Γ) ⊇ Γ
  wk = weak id

  weakening : ∀ {t t' Γ} → Value Γ t → Value (t' ∷ Γ) t
  weakening = weaken-Value wk


  readback : ∀ {i Γ t} → Value Γ t → Delay i (Normal Γ t)
  nereadback : ∀ {i Γ t} → Neutral Value Γ t → Delay i (Neutral Normal Γ t)
  eta : ∀ {i Γ t t'} → Value Γ (t' ⇒ t) → ∞Delay i (Normal (t' ∷ Γ) t)

  readback {t = ι} (neutral x) = map neutral (nereadback x)
  readback {t = t₁ ⇒ t₂} v = map `λ (later (eta v))
  force (eta v)
    = do
         e ← apply (weakening v) (neutral (var (here refl)))
         readback e
  nereadback (var x) = now (var x)
  nereadback (w ∙ v)
    = do
         m ← nereadback w
         map (m ∙_) (readback v)


  idEnv : ∀ Γ → Env Γ Γ
  idEnv [] = []
  idEnv (t ∷ Γ) = neutral (var (here refl)) ∷ weaken-Env wk (idEnv Γ)


  nf : ∀ {Γ t} → Γ ⊢ t → Delay ∞ (Normal Γ t)
  nf {Γ} Γ⊢t
    = do
        v ← eval Γ⊢t (idEnv Γ)
        readback v
