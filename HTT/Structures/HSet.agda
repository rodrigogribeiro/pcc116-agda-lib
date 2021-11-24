{-# OPTIONS --without-K #-}

module HTT.Structures.HSet where

open import HTT.Basics.BasicTypes


-- definition of set

isSet : ∀ {U} → Type U → Type U
isSet A = (x y : A)(p q : x ≡ y) → p ≡ q

-- type bool is a set

Bool-isSet : isSet Bool
Bool-isSet false false refl refl = refl
Bool-isSet true true refl refl   = refl

-- product is closed under isSet

×-isSet : ∀ {U V}{A : Type U}{B : Type V} →
            isSet A →
            isSet B →
            isSet (A × B)
×-isSet SA SB (x , y) (x' , y') p q
  = begin
      p                           ≡⟨ ×-≡-η ⟩
      ×-≡ (ap fst p) (ap snd p)   ≡⟨ ap2 ×-≡
                                         (SA x x' (ap fst p) (ap fst q))
                                         (SB y y' (ap snd p) (ap snd q)) ⟩
      ×-≡ (ap fst q) (ap snd q)   ≡⟨ ! ×-≡-η ⟩
      q
    ∎

-- naturals are a set

ℕ-isSet : isSet ℕ
ℕ-isSet zero zero refl refl = refl
ℕ-isSet zero (suc m) () q
ℕ-isSet (suc n) zero () q
ℕ-isSet (suc n) (suc m) p q
  = begin
      p                   ≡⟨ suc-pred-≡ p ⟩
      ap suc (ap pred p)  ≡⟨ ap (ap suc) (ℕ-isSet n m _ _) ⟩
      ap suc (ap pred q)  ≡⟨ (! (suc-pred-≡ q)) ⟩
      q
    ∎
