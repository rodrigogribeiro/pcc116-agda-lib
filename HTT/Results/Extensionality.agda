{-# OPTIONS --without-K #-}

module HTT.Results.Extensionality where

open import HTT.Basics.BasicTypes
open import HTT.Structures.Contractible
open import HTT.Univalence.Equivalence
open import HTT.Univalence.Axiom

-- Definition of paths

Path : ∀ {U}(A : Type U) → Type U
Path A = Σ (λ (x : A) → Σ (λ (y : A) → x ≡ y))

-- Getting the source of a path

Path-src : ∀ {U}{A : Type U} → Path A → A
Path-src (x , _) = x

-- Getting the target of a path

Path-tgt : ∀ {U}{A : Type U} → Path A → A
Path-tgt (_ , (y , _)) = y

Path-≡ : ∀ {U}{A : Type U}(p : Path A) →
           Path-src p ≡ Path-tgt p
Path-≡ (x , (y , p)) = p

-- converting an identity to a path

Path-of : ∀ {U}{A : Type U}{x y : A}(p : x ≡ y) → Path A
Path-of {x = x}{y = y} p = x , (y , p)

-- Constant path

Path-cst : ∀ {U}{A : Type U} → A → Path A
Path-cst x = x , (x , refl)

-- contraction of paths.

Path-contract : ∀ {U}{A : Type U} → Path A ≃ A
Path-contract = Path-src , ((Path-cst , (λ { (_ , (_ , refl)) → refl }))
                                      , (Path-cst , (λ _ → refl)))

-- definition of homotopy

Homotopy : ∀ {U V}(A : Type U)(B : A → Type V) → Type (U ⊔ V)
Homotopy A B = (x : A) → Path (B x)

-- source and target of a homotopy

Homotopy-src : ∀ {U V}{A : Type U}{B : A → Type V} →
                 Homotopy A B → (x : A) → B x
Homotopy-src h x = Path-src (h x)

Homotopy-tgt : ∀ {U V}{A : Type U}{B : A → Type V} →
                 Homotopy A B → (x : A) → B x
Homotopy-tgt h x = Path-tgt (h x)

Homotopy-~ : ∀ {U V}{A : Type U}{B : A → Type V}
               (h : Homotopy A B) → Homotopy-src h ~ Homotopy-tgt h
Homotopy-~ h x = Path-≡ (h x)

Homotopy-of : ∀ {U V}{A : Type U}{B : A → Type V}{f g : (x : A) → B x} →
                f ~ g → Homotopy A B
Homotopy-of h x = Path-of (h x)

Homotopy-cst : ∀ {U V}{A : Type U}{B : A → Type V} → ((x : A) → B x) → Homotopy A B
Homotopy-cst f = Homotopy-of (λ x → refl {x = f x})

-- homotopy is equivalent to Path

≃-to : ∀ {U V}{A : Type U}{B B' : Type V} →
         B ≃ B' → (A → B) ≃ (A → B')
≃-to {U}{V}{A}{B} e = (λ f x → (≃-→ e) (f x)) , lem e
  where
    lem : {B B' : Type V}(e : B ≃ B') →
          isEquiv (λ (f : A → B) x → (≃-→ e) (f x))
    lem  = ≃-ind (λ {B} e → isEquiv (λ (f : A → B) x → (≃-→ e) (f x)))
                 λ {B} → snd (≃-refl {A = A → B})

Homotopy-≃-Path : ∀ {U V}{A : Type U}{B : Type V} →
                    Homotopy A (λ _ → B) ≃ Path (A → B)
Homotopy-≃-Path {U}{V}{A}{B}
  = begin-≃
      Homotopy A (λ _ → B) ≃⟨ ≃-refl ⟩
      (A → Path B)         ≃⟨ ≃-to Path-contract ⟩
      (A → B)              ≃⟨ ≃-sym Path-contract ⟩
      Path (A → B)
    ≃-∎

-- proving non-dependent extensionality

FE : (U V : Universe) → Type ((U ⊔ V) ⁺)
FE U V = {A : Type U}{B : Type V}{f g : A → B} →
         ((x : A) → f x ≡ g x) → f ≡ g

funext : ∀ {U V} → FE U V
funext {A = A}{B = B}{f = f}{g = g} h
  = ap (λ h x → Homotopy-tgt h x) p
    where
      p : Homotopy-cst f ≡ Homotopy-of h
      p = ≃-inj Homotopy-≃-Path refl

