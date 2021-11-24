{-# OPTIONS --without-K #-}

module HTT.Basics.Nat where

open import HTT.Basics.Universes
open import HTT.Basics.Id

-- natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred 0 = 0
pred (suc n) = n

-- some lemmas

≡-suc : {n m : ℕ} → n ≡ m → suc n ≡ suc m
≡-suc = ap suc

suc-≡ : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-≡ refl = refl

suc-pred-≡ : ∀ {n m : ℕ}(p : suc n ≡ suc m) → p ≡ ap suc (ap pred p)
suc-pred-≡ refl = refl

-- ordering

data _≤_ : ℕ → ℕ → Type U₀ where
  z≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m

_<_ : ℕ → ℕ → Type U₀
n < m = suc n ≤ m

-- ≤ is a partial order

n≤1+n : ∀ (n : ℕ) → n ≤ suc n
n≤1+n zero = z≤n
n≤1+n (suc n) = s≤s (n≤1+n n)


≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
≤-trans z≤n m≤p = z≤n
≤-trans (s≤s n≤m) (s≤s m≤p) = s≤s (≤-trans n≤m m≤p)

≤-antisym : ∀ {n m} → n ≤ m → m ≤ n → n ≡ m
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s n≤m) (s≤s m≤n) = ap suc (≤-antisym n≤m m≤n)

-- recursion downwards

rec-down : ∀ {U}(P : ℕ → Type U)(m : ℕ) → P m     →
             ((n : ℕ) → n < m → P (suc n) → P n) →
             (n : ℕ) → n ≤ m → P n
rec-down P zero Pm IH .0 z≤n = Pm
rec-down P (suc m) Pm IH .0 z≤n = IH zero (s≤s z≤n)
                                    (rec-down (λ z → P (suc z)) m Pm (λ n z → IH (suc n) (s≤s z)) zero
                                     z≤n)
rec-down P (suc m) Pm IH .(suc _) (s≤s n≤m) = rec-down (λ z → P (suc z)) m Pm (λ n z → IH (suc n) (s≤s z)) _ n≤m
