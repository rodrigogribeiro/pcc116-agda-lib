module Data.Nat.Le where

open import Basics.Admit

open import Basics.Level

open import Data.Bool.Bool
open import Data.Nat.Nat
open import Data.Nat.NatTheorems

open import Relation.Equality.Propositional


-- definition of the ≤ relation

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {n m} → n ≤ m
                → (suc n) ≤ (suc m)

-- definition of <

infix 4 _<_

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- ≤ is a ordering relation

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl


≤-trans : ∀ {n m p} → n ≤ m
                    → m ≤ p
                    → n ≤ p
≤-trans z≤n m≤p = z≤n
≤-trans (s≤s n≤m) (s≤s m≤p) = s≤s (≤-trans n≤m m≤p)

≤-antisym : ∀ {x y} → x ≤ y →
                      y ≤ x →
                      x ≡ y
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x≤y) (s≤s y≤x)
   = cong {l = lzero} suc (≤-antisym x≤y y≤x)


-- ≤ is total

data Total : ℕ → ℕ → Set where
  forward : ∀ {n m} →
              n ≤ m →
              Total n m
  flipped : ∀ {n m} →
              m ≤ n →
              Total n m


≤-total : ∀ (n m : ℕ) → Total n m
≤-total zero m = forward z≤n
≤-total (suc n) zero = flipped z≤n
≤-total (suc n) (suc m) with ≤-total n m
...| forward n≤m = forward (s≤s n≤m)
...| flipped m≤n = flipped (s≤s m≤n)

-- basic facts about ordering 

≤-suc : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
≤-suc z≤n = z≤n
≤-suc (s≤s n≤m) = s≤s (≤-suc n≤m)

≤-+-left : ∀ {n m p} → n ≤ m → n ≤ p + m
≤-+-left {p = zero} n≤m = n≤m
≤-+-left {n = .0} {p = suc p} z≤n = z≤n
≤-+-left {n = (suc n)}{m = suc m} {p = suc p} (s≤s n≤m)
  with ≤-+-left {p = p} n≤m
...| n≤p+m rewrite +-comm p (suc m) | +-comm m p
  = s≤s (≤-suc n≤p+m)

-- monotonicity of addition

-- Exercise 1.

+-mono-left : ∀ {n m p} → n ≤ m → p + n ≤ p + m
+-mono-left = admit

+-mono-right : ∀ {n m p} → n ≤ m → n + p ≤ m + p
+-mono-right = admit

+-mono-≤ : ∀ {n m p q} → n ≤ m → p ≤ q → (n + p) ≤ (m + q)
+-mono-≤ = admit

-- Exercise 2. Implement a less or equal than test that results on a boolean.

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ m = true
suc n ≤ᵇ zero = false
suc n ≤ᵇ suc m = n ≤ᵇ m

_<?_ : ℕ → ℕ → Bool
n <? m = suc n ≤ᵇ m

-- Exercise 3. Prove the soundness and completeness of your function ≤ᵇ.

≤ᵇ-sound : ∀ {n m} → n ≤ᵇ m ≡ true → n ≤ m
≤ᵇ-sound = admit

≤ᵇ-complete : ∀ {n m} → n ≤ m → n ≤ᵇ m ≡ true
≤ᵇ-complete = admit
