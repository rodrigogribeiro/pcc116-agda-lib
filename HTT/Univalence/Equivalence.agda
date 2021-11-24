{-# OPTIONS --without-K #-}

module HTT.Univalence.Equivalence where

open import HTT.Basics.BasicTypes
open import HTT.Structures.Contractible
open import HTT.Univalence.IdProperties

-- homotopic equivalence

infix 6 _~_

_~_ : ∀ {U V}{A : Type U}{B : A → Type V}
        (f g : (x : A) → B x) → Type (U ⊔ V)
f ~ g = ∀ x → f x ≡ g x


isQInv : ∀ {U V}{A : Type U}{B : Type V} →
         (A → B) → Type (U ⊔ V)
isQInv {A = A}{B = B} f
  = Σ {A = B → A}(λ g → ((g ∘ f) ~ id) × ((f ∘ g) ~ id))


-- equivalence

isEquiv : ∀ {U V}{A : Type U}{B : Type V} →
          (A → B) → Type (U ⊔ V)
isEquiv {A = A}{B = B} f
  = Σ {A = B → A}(λ g → (g ∘ f) ~ id) ×
    Σ {A = B → A}(λ g → (f ∘ g) ~ id)


isQInv-isEquiv : ∀ {U V}{A : Type U}{B : Type V}{f : A → B} →
                 isQInv f → isEquiv f
isQInv-isEquiv (g , (gf , fg)) = (g , gf) , (g , fg)

-- contractibility

fib : ∀ {U V}{A : Type U}{B : Type V} →
      (A → B) → B → Type (U ⊔ V)
fib {A = A} f y = Σ {A = A}(λ x → f x ≡ y)

isContrMap : ∀ {U V}{A : Type U}{B : Type V} →
               (A → B) → Type (U ⊔ V)
isContrMap {B = B} f = (y : B) → isContr (fib f y)


-- equivalence of types

_≃_ : ∀ {U V} → Type U → Type V → Type (U ⊔ V)
A ≃ B = Σ {A = A → B} isEquiv

≃-refl : ∀ {U}{A : Type U} → A ≃ A
≃-refl = id , ((id , (λ x → refl))
       , (id , (λ x → refl)))

private
  trans : ∀ {U V W}{A : Type U}{B : Type V}{C : Type W} →
            {i : C → B}{h : B → C}{f : A → B}{g : B → A} →
            {x : A} → ((g ∘ i) ∘ (h ∘ f)) x ≡ (g ∘ f) x →
            (g ∘ f) x ≡ x → ((g ∘ i) ∘ (h ∘ f)) x ≡ x
  trans p q rewrite p = q

≃-trans : ∀ {U V W}{A : Type U}{B : Type V}{C : Type W} →
          A ≃ B → B ≃ C → A ≃ C
≃-trans (f , ((g , gf) , (g' , gf'))) (h , ((i , ih) , (i' , hi')))
  = (h ∘ f) , (((g ∘ i) , λ x → trans {i = i}
                                       {h = h}
                                       {f = f}
                                       {g = g}
                                       (ap g (ih (f x))) (gf x))
            , ((g' ∘ i') , (λ x → trans {i = f}
                                         {h = g'}
                                         {f = i'}
                                         {g = h}
                                         (ap h (gf' (i' x))) (hi' x))))

≃-sym : ∀ {U V}{A : Type U}{B : Type V} → A ≃ B → B ≃ A
≃-sym {B = B} (f , ((g , gf) , (g' , fg')))
  = g , ((f , left) , (f , gf))
    where
      trap : ∀ {x} → g x ≡ g ((f ∘ g') x) →
                      (g ∘ f) (g' x) ≡ g' x →
                      g x ≡ g' x
      trap p q rewrite p = q

      g-g' : (x : B) → g x ≡ g' x
      g-g' x = trap (! ap g (fg' x)) (gf (g' x))

      trick : ∀ {x} → f (g x) ≡ f (g' x) →
                       (f ∘ g') x ≡ x →
                       f (g x) ≡ x
      trick p q rewrite p = q

      left : (x : B) → f (g x) ≡ x
      left x = trick (ap f (g-g' x)) (fg' x)


≃-→ : ∀ {U V}{A : Type U}{B : Type V} → A ≃ B → A → B
≃-→ (f , _) = f

≃-← : ∀ {U V}{A : Type U}{B : Type V} → A ≃ B → B → A
≃-← (_ , ((g , _) , _)) = g

≃-η : ∀ {U V}{A : Type U}{B : Type V}(e : A ≃ B)(x : A) →
        x ≡ ≃-← e (≃-→ e x)
≃-η (f , ((g , gl) , (h , hr))) x = ! gl x

≃-ε : ∀ {U V}{A : Type U}{B : Type V}(e : A ≃ B)(y : B) →
      ≃-→ e (≃-← e y) ≡ y
≃-ε (f , ((g , gl) , (h , hr))) y
  = begin
      f (g y)         ≡⟨ (! ap (λ y → f (g y)) (hr y)) ⟩
      f (g (f (h y))) ≡⟨ ap f (gl (h y)) ⟩
      f (h y)         ≡⟨ hr y ⟩
      y
    ∎

≃-inj : ∀ {U V}{A : Type U}{B : Type V}
          (e : A ≃ B){x y : A} → ≃-→ e x ≡ ≃-→ e y → x ≡ y
≃-inj e {x}{y} p
  = begin
      x                  ≡⟨ ≃-η e x ⟩
      ≃-← e (≃-→ e x)  ≡⟨ ap (≃-← e) p ⟩
      ≃-← e (≃-→ e y)  ≡⟨ (! ≃-η e y) ⟩
      y
    ∎

id-to-equiv' : ∀ {U}{A B : Type U} → A ≡ B → A ≃ B
id-to-equiv' refl = id , ((id , λ _ → refl)
                       , (id , (λ _ → refl)))

coerce-isEquiv : ∀ {U}{A B : Type U}(p : A ≡ B) → isEquiv (coerce p)
coerce-isEquiv refl = (id , (λ x → refl)) , (id , λ x → refl)


id-to-equiv : ∀ {U}{A B : Type U} → A ≡ B → A ≃ B
id-to-equiv p = coerce p , coerce-isEquiv p


-- equational reasoning

infix 1 begin-≃_

begin-≃_ : ∀ {l}{A B : Type l} → A ≃ B → A ≃ B
begin-≃_ x≡y = x≡y

infixr 2 step-≃

step-≃ : ∀ {l}(A : Type l) {B C : Type l} → B ≃ C → A ≃ B → A ≃ C
step-≃ _ A≡B B≡C = ≃-trans B≡C A≡B

syntax step-≃  x y≡z x≡y = x ≃⟨  x≡y ⟩ y≡z

infix 3 _≃-∎

_≃-∎ : ∀ {l}(A : Type l) → A ≃ A
_≃-∎ _ = ≃-refl
