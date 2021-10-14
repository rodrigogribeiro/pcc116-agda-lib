module Prelude.Nat where

open import Data.Bool.Bool
open import Data.Nat.Nat
open import Data.Nat.Le renaming ( _≤_       to _≤N_
                                 ; ≤-refl    to ≤N-refl
                                 ; ≤-antisym to ≤N-antisym
                                 ; ≤-trans   to ≤N-trans
                                 )

open import Prelude.Classes

open import Relation.Equality.Propositional

variable n m : ℕ

_≡ᵇ_ : ℕ → ℕ → Bool
zero ≡ᵇ zero = true
suc _ ≡ᵇ zero = false
zero ≡ᵇ suc _ = false
suc n ≡ᵇ suc m = n ≡ᵇ m

instance
  ≡-dec : {p : T (n ≡ᵇ m)} → n ≡ m
  ≡-dec {n = zero} {m = zero} = refl
  ≡-dec {n = suc n} {m = suc m}{p = p} = cong suc (≡-dec {p = p})

_<ᵇ_ : ℕ → ℕ → Bool
_ <ᵇ zero = false
zero <ᵇ suc _ = true
suc n <ᵇ suc m = n <ᵇ m

instance
  ≤-dec : {p : T (n <ᵇ suc m)} → n ≤N m
  ≤-dec {n = zero} {m = m} = z≤n
  ≤-dec {n = suc n} {m = suc m} {p = p}
    = s≤s (≤-dec {p = p})

instance
  Eq-ℕ : Eq ℕ
  _==_    {{Eq-ℕ}} = _≡_ {A = ℕ}
  ≡-refl  {{Eq-ℕ}} = refl
  ≡-sym   {{Eq-ℕ}} = sym
  ≡-trans {{Eq-ℕ}} = trans

instance
  Ord-ℕ : Ord ℕ
  _≤_ {{Ord-ℕ}}       = _≤N_
  ≤-refl {{Ord-ℕ}}    = ≤N-refl
  ≤-antisym {{Ord-ℕ}} = ≤N-antisym
  ≤-trans {{Ord-ℕ}}   = ≤N-trans

triℕ : (x y : ℕ) → Tri x y
triℕ zero zero = equal
triℕ zero (suc y) = less
triℕ (suc x) zero = greater
triℕ (suc x) (suc y) with triℕ x y
...| less {{x≤y}} = less {{x≤y = s≤s x≤y}}
...| equal {{ x≡y }} = equal {{x≡y = cong suc x≡y}}
...| greater {{x≥y}} = greater {{ x≥y = s≤s x≥y }}

instance
  Compare-ℕ : Compare ℕ
  Ord-A   {{Compare-ℕ}} = Ord-ℕ
  compare {{Compare-ℕ}} = triℕ
