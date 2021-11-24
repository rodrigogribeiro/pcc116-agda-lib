module HTT.Results.Roots where

open import HTT.Basics.BasicTypes
open import HTT.Structures.HProp
open import HTT.Structures.HSet
open import HTT.Structures.Existential
open import HTT.Structures.Truncation

-- predicate for the smallest number satisfying a property

isFirst : ∀ {U}(P : ℕ → Type U) → ℕ → Type U
isFirst P n = P n × ((m : ℕ) → P m → n ≤ m)

-- the smallest is unique

isFirst-≡ : ∀ {U}(P : ℕ → Type U){m n : ℕ} →
            isFirst P m → isFirst P n → m ≡ n
isFirst-≡ P {m}{n} (Pm , Fm) (Pn , Fn)
  = ≤-antisym (Fm n Pn) (Fn m Pm)

-- isFirst is a proposition

first-isProp : ∀ {U}(P : ℕ → Type U) → ((n : ℕ) → isProp (P n)) → isProp (Σ (isFirst P))
first-isProp P prop
  = Σ-isProp (λ n → ×-isProp (prop n)
                              (Π-isProp (λ n → Π-isProp (λ Pn → ≤-isProp))))
             (λ n m → isFirst-≡ P)

-- type of the smallest number greater than k

isFirst-from : ∀ {U} → ℕ → (P : ℕ → Type U) → ℕ → Type U
isFirst-from k P n = isFirst (λ n → (k ≤ n) × P n) n

-- finding the first root from a given number

find-first-from : ∀ {U}(P : ℕ → Type U) → ((n : ℕ) → isDec (P n)) →
                    (m : ℕ) → P m → (k : ℕ) → k ≤ m →
                    Σ {A = ℕ} (λ n → isFirst-from k P n)
find-first-from P dec m Pm k k≤m
  = rec-down (λ k → Σ (λ n → isFirst-from k P n))
             m
             (m , ((≤-refl , Pm) , λ { _ (m≤n , _ ) → m≤n}))
             IH
             k
             k≤m
    where
      split-≤ : ∀ {n m} → n ≤ m → (n < m) + (n ≡ m)
      split-≤ {zero} {zero} n≤m = inr refl
      split-≤ {zero} {suc m} n≤m = inl (s≤s z≤n)
      split-≤ {suc n} {suc m} (s≤s n≤m) with split-≤ n≤m
      ...| inl n<m = inl (s≤s n<m)
      ...| inr n≡m = inr (ap suc n≡m)

      IH : ∀ (k : ℕ) → k < m → Σ (λ n → isFirst-from (suc k) P n) →
           Σ (λ n → isFirst-from k P n)
      IH k k<n (n , Pn) with dec k
      ...| inl Pk = k , ((≤-refl , Pk) , (λ { _ (k≤n , _) → k≤n}))
      IH k (s≤s k<n) (n , ((k+1<n , Pn) , Fn)) | inr ¬Pk
        = n , (((≤-trans (n≤1+n k) k+1<n) , Pn) ,
              λ {i (k≤i , Pi) → case split-≤ k≤i of λ { (inl k<i) → Fn i (k<i , Pi) ;
                                                          (inr k≡i) → ⊥-elim (¬Pk (subst P (! k≡i) Pi))}})


find-first : ∀ {U}(P : ℕ → Type U) → ((n : ℕ) → isDec (P n)) →
             (m : ℕ) → P m → Σ (isFirst P)
find-first P dec m Pm with find-first-from P dec m Pm 0 z≤n
... | n , ((_ , Pn) , Fn) = n , (Pn , (λ x x₁ → Fn x (z≤n , x₁)))

-- extracting the root

_≟_ : (n m : ℕ) → isDec (n ≡ m)
zero ≟ zero = inl refl
zero ≟ suc m = inr (λ ())
suc n ≟ zero = inr (λ ())
suc n ≟ suc m with n ≟ m
...| inl p = inl (ap suc p)
...| inr q = inr (λ x → q (suc-≡ x))


extract-first-root : ∀ (f : ℕ → ℕ) → ∃ ℕ (λ n → f n ≡ 0) → Σ (isFirst (λ n → f n ≡ 0))
extract-first-root f E
  = ∥∥-rec (first-isProp P (λ n → ℕ-isSet (f n) 0))
           (λ {(n , Pn) → find-first P (λ n → f n ≟ 0) n Pn})
           E
    where
      P : ℕ → Type U₀
      P n = f n ≡ 0

extract-root : ∀ (f : ℕ → ℕ) → ∃ ℕ (λ n → f n ≡ 0) → Σ (λ n → f n ≡ 0)
extract-root f E with extract-first-root f E
...| n , (Pn , _) = n , Pn
