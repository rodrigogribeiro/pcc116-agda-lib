module Data.Nat.NatTheorems where

open import Basics.Admit
open import Data.Bool.Bool
open import Data.Nat.Nat

open import Relation.Equality.Propositional

-- properties of addition

+-zero-left : ∀ (n : ℕ) → 0 + n ≡ n
+-zero-left n = refl

+-zero-right : ∀ (n : ℕ) → n + 0 ≡ n
+-zero-right zero    = refl
+-zero-right (suc n)
  = begin
      (suc n) + 0 ≡⟨⟩
      suc (n + 0) ≡⟨ cong suc (+-zero-right n) ⟩
      suc n
    ∎

+-assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ x + y + z
+-assoc zero y z = refl
+-assoc (suc x) y z
  = begin
      (suc x) + (y + z) ≡⟨⟩
      suc (x + (y + z)) ≡⟨ cong suc (+-assoc x y z) ⟩
      suc (x + y + z)   ≡⟨⟩
      (suc x) + y + z
    ∎

+-suc : ∀ (n m : ℕ) → suc (n + m) ≡ n + suc m
+-suc zero m = refl
+-suc (suc n) m rewrite +-suc n m = refl

+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm zero m rewrite +-zero-right m = refl
+-comm (suc n) m
  = begin
      suc n + m   ≡⟨⟩
      suc (n + m) ≡⟨ cong suc (+-comm n m) ⟩
      suc (m + n) ≡⟨ +-suc m n ⟩
      m + suc n
    ∎

-- properties of multiplication

*-distr-+-r : ∀ (x y z : ℕ) → (x + y) * z ≡ (x * z) + (y * z)
*-distr-+-r zero y z = refl
*-distr-+-r (suc x) y z rewrite *-distr-+-r x y z |
                                +-assoc z (x * z) (y * z) = refl

*-assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ x * y * z
*-assoc zero y z = refl
*-assoc (suc x) y z
  = begin
      (suc x) * (y * z)     ≡⟨⟩
      (y * z) + x * (y * z) ≡⟨ cong ((y * z) +_) (*-assoc x y z) ⟩
      (y * z) + x * y * z   ≡⟨ sym (*-distr-+-r y (x * y) z) ⟩
      (y + x * y) * z       ≡⟨⟩
      ((suc x) * y) * z
   ∎

-- Exercise 1

*-zero-right : ∀ (n : ℕ) → n * 0 ≡ 0
*-zero-right = admit

-- Exercise 2

*-suc : ∀ (m n : ℕ) → m + m * n ≡ m * suc n
*-suc = admit

-- Exercise 3

*-comm : ∀ (n m : ℕ) → n * m ≡ m * n
*-comm = admit

-- Exercise 4

*-distr-+-l : ∀ (x y z : ℕ) → x * (y + z) ≡ (x * y) + (x * z)
*-distr-+-l = admit

-- Exercise 5

-zero-l : ∀ (n : ℕ) → 0 - n ≡ 0
-zero-l = admit

-- Exercise 6

-assoc : ∀ (x y z : ℕ) → x - y - z ≡ x - (y + z)
-assoc = admit

-- Exercise 7

^-distr-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distr-+-* = admit

-- Exercise 8

^-distr-*-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distr-*-* = admit


-- Exercise 9

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc = admit 

-- comparison

≡B-sound : ∀ {n m} → n ≡B m ≡ true → n ≡ m
≡B-sound {zero} {zero} n≡Bm = refl
≡B-sound {suc n} {suc m} n≡Bm = cong suc IH
  where
     IH : n ≡ m
     IH = ≡B-sound {n}{m} n≡Bm

≡B-refl : ∀ (n : ℕ) → n ≡B n ≡ true
≡B-refl zero = refl
≡B-refl (suc n) = ≡B-refl n

≡B-complete : ∀ {n m} → n ≡ m → n ≡B m ≡ true
≡B-complete {n} refl = ≡B-refl n

-- results about even and odd

even : ℕ → Bool
odd  : ℕ → Bool

even zero    = true
even (suc n) = odd n

odd zero     = false
odd (suc n) = even n

even-not-odd : (n : ℕ) → even n ≡ not (odd n)
odd-not-even : (n : ℕ) → odd n ≡ not (even n)

even-not-odd zero = refl
even-not-odd (suc n) = odd-not-even n

odd-not-even zero = refl
odd-not-even (suc n) = even-not-odd n

-- Exercise 10

+-even : ∀ {n m : ℕ} → even n ≡ true → even m ≡ true → even (n + m) ≡ true
+-even = admit

-- Exercise 11 

+-odd-even : ∀ {n m : ℕ} → odd n ≡ true → even m ≡ true → odd (n + m) ≡ true
+-odd-even = admit
