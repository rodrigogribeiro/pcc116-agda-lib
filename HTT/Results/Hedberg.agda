{-# OPTIONS --without-K #-}

module HTT.Results.Hedberg where

open import HTT.Structures.HProp
open import HTT.Structures.HSet
open import HTT.Basics.BasicTypes


-- proof of Hedberg theorem: every type with decidable equality is a Set

isDecEq : ∀ {U} → Type U → Type U
isDecEq A = (x y : A) → isDec (x ≡ y)

-- double negation implies decidability on types

isNNE : ∀ {U} → Type U → Type U
isNNE A = (¬ (¬ A)) → A

isNNEq : ∀ {U} → Type U → Type U
isNNEq A = (x y : A) → isNNE (x ≡ y)

isDecEq-isNNE : ∀ {U}{A : Type U} → isDec A → isNNE A
isDecEq-isNNE (inl a) a' = a
isDecEq-isNNE (inr a) a' = ⊥-elim (a' a)

-- double negation Id

nneId : ∀ {U}{A : Type U} → isNNEq A → {x y : A} →
            (p : x ≡ y) → x ≡ y
nneId N {x}{y} p = N x y (λ k → k p)

nneIdCannonical : ∀ {U}{A : Type U} → (N : isNNEq A) →
                    {x y : A}(p q : x ≡ y) → nneId N p ≡ nneId N q
nneIdCannonical N {x}{y} p q = ap (N x y)
                                  (¬-isProp (λ k → k p)
                                            (λ k → k q))

nneIdEq : ∀ {U}{A : Type U}(N : isNNEq A){x y : A}(p : x ≡ y) →
            p ≡ ! (nneId N refl) ∙ nneId N p
nneIdEq N {x}{y} refl = ! ∙-cancel-right (N x x (λ z → z refl))

-- proving Hedberg theorem

Hedberg : ∀ {U}{A : Type U}(N : isNNEq A) → isSet A
Hedberg N x y p q
  = begin
      p                                ≡⟨ nneIdEq N p ⟩
      (! (nneId N refl) ∙ (nneId N p)) ≡⟨ ap (λ nnp → ! (nneId N refl) ∙ nnp)
                                             (nneIdCannonical N p q) ⟩
      (! (nneId N refl) ∙ (nneId N q)) ≡⟨ (! (nneIdEq N q)) ⟩
      q
    ∎
