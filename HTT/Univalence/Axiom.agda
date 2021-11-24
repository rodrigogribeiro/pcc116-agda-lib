{-# OPTIONS --without-K #-}

module HTT.Univalence.Axiom where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HProp
open import HTT.Structures.Contractible
open import HTT.Univalence.IdProperties
open import HTT.Univalence.Equivalence

-- axiom of univalence

postulate univalence : ∀ {U}{A B : Type U} → isEquiv (id-to-equiv {U}{A}{B})

ua-equiv : ∀ {U}{A B : Type U} → (A ≡ B) ≃ (A ≃ B)
ua-equiv = id-to-equiv , univalence

ua : ∀ {U}{A B : Type U} → A ≃ B → A ≡ B
ua f = ≃-← ua-equiv f

ua-comp : ∀ {U}{A B : Type U}(e : A ≃ B) → coerce (ua e) ≡ fst e
ua-comp {A = A}{B = B} e = ap fst (≃-ε ua-equiv e)

ua-ext : ∀ {U}{A B : Type U}{p : A ≡ B} → p ≡ ua (id-to-equiv p)
ua-ext {p = p} = ≃-η ua-equiv p

-- equivalence between products

×-≃ : ∀ {U V}{A : Type U}{B : Type V}{x y : A × B} →
        (x ≡ y) ≃ ((fst x ≡ fst y) × (snd x ≡ snd y))
×-≃ {x = x}{y = y} = f , ((g , (λ {refl → refl})) , (g , λ {(refl , refl) → refl}))
                     where
                       f : x ≡ y → (fst x ≡ fst y) × (snd x ≡ snd y)
                       f refl = refl , refl

                       g : (fst x ≡ fst y) × (snd x ≡ snd y) → x ≡ y
                       g (refl , refl) = refl


-- encoding identities between ℕ

code : ℕ → ℕ → Type U₀
code zero zero       = ⊤
code zero (suc m)    = ⊥
code (suc n) zero    = ⊥
code (suc n) (suc m) = code n m

-- proving that n ≡ m ≃ code n m

enc : ∀ {n m : ℕ} → n ≡ m → code n m
enc {zero} {.zero} refl     = ⋆
enc {suc n} {.(suc n)} refl = enc {n} {n} refl


dec : ∀ {n m} → code n m → n ≡ m
dec {zero} {zero} ⋆   = refl
dec {suc n} {suc m} p = ap suc (dec p)


ℕ-eq : (n m : ℕ) → (n ≡ m) ≃ (code n m)
ℕ-eq n m = enc , ((dec , dec-enc) , (dec , enc-dec {n}))
  where
    dec-enc : {n m : ℕ}(p : n ≡ m) → dec (enc p) ≡ p
    dec-enc {zero}{.zero} refl = refl
    dec-enc {suc n}{.(suc n)} refl = ap (ap suc) (dec-enc refl)

    enc-suc : {n m : ℕ}(p : n ≡ m) → enc (ap suc p) ≡ enc p
    enc-suc refl = refl

    enc-dec : {n m : ℕ}(p : code n m) → enc (dec {n} p) ≡ p
    enc-dec {zero}{zero} ⋆ = refl
    enc-dec {suc n}{suc m} p rewrite enc-suc (dec {n}{m} p) = enc-dec {n}{m} p


-- If ¬ A holds, then A is equivalent to ⊥

¬-≃-⊥ : ∀ {U}{A : Type U} → ¬ A → A ≃ ⊥
¬-≃-⊥ na = na , ((⊥-elim , (λ x → ⊥-elim (na x)))
                 , (⊥-elim , λ x → ⊥-isProp _ _))

Prop-≃-⊥ : ∀ {U}{A : Type U} → isProp A → ¬ A → A ≃ ⊥
Prop-≃-⊥ PA na = ¬-≃-⊥ na


Contr-≃-⊤ : ∀ {U}{A : Type U} → isContr A → A ≃ ⊤
Contr-≃-⊤ {A = A}(x , p)
  = f , ((g , p) , (g , (λ { ⋆ → refl})))
    where
      f : A → ⊤
      f _ = ⋆

      g : ⊤ → A
      g _ = x

Contr-≃-Lift-⊤ : ∀ {U}{A : Type U} → isContr A → A ≃ Lift U ⊤
Contr-≃-Lift-⊤ {U = U}{A = A}(x , p)
  = f , ((g , p) , (g , (λ {(lift ⋆) → refl})))
    where
      f : A → Lift U ⊤
      f _ = lift ⋆

      g : Lift U ⊤ → A
      g (lift ⋆) = x

aProp-isContr : ∀ {U}{A : Type U} → isProp A → A → isContr A
aProp-isContr PA x = x , (PA x)

Prop-≃-⊤ : ∀ {U}{A : Type U} → isProp A → A → A ≃ ⊤
Prop-≃-⊤ PA x = Contr-≃-⊤ (aProp-isContr PA x)


-- properties of equivalence

≃-ap : ∀ {U V}{A B : Type U}(f : Type U → Type V) → A ≃ B → f A ≃ f B
≃-ap f e = id-to-equiv (ap f (ua e))

≃-ind : ∀ {U V}(P : {A B : Type U} → A ≃ B → Type V) →
          ({A : Type U} → P (≃-refl {A = A})) →
          {A B : Type U}(e : A ≃ B) → P e
≃-ind {U = U} P r {A} {B} e
  = subst P (≃-ε ua-equiv e) (lem (ua e))
    where
      lem : (p : A ≡ B) → P (id-to-equiv p)
      lem refl = r
