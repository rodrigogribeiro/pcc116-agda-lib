module HTT.Results.Diaconescu where

open import HTT.Basics.BasicTypes
open import HTT.Structures.Existential
open import HTT.Structures.Disjunction
open import HTT.Structures.HProp
open import HTT.Structures.Truncation
open import HTT.Results.Choice


-- non-empty set of booleans

module _ {U}{A : Type U}(x : A)(P : isProp A) where

  u : Type (U ⁺)
  u = Σ {A = Bool → Type U} (λ Q → ∃ Bool Q)

  F : u
  F = (λ b → (b ≡ false) ∨ A) , ∣  false  , in-left refl  ∣

  T : u
  T = (λ b → (b ≡ true) ∨ A) , ∣  true  , in-left refl  ∣

  postulate propext : PE {U}

  F≡T : F ≡ T
  F≡T = Σ-≡ (extensionality (λ {false → propext (∥∥-isProp _)
                                                 (∥∥-isProp _)
                                                 ((λ _ → in-right x) , (λ _ → in-right x)) ;
                                true → propext (∥∥-isProp _)
                                                (∥∥-isProp _)
                                                ((λ _ → in-right x) , λ _ → in-right x) }))
                            (∥∥-isProp _ (subst (∃ Bool) _ (snd F)) (snd T))

  dec : ((Q : u) → Σ {A = Bool} (fst Q)) → A ∨ (¬ A)
  dec f with inspect (f F) | inspect (f T)
  ...| (false , p ) , _ | (false , q ) , _
    = ∥∥-rec (∥∥-isProp _) (λ z → +-elim z (λ ()) (λ a → in-left a)) q
  ...| (false , p ) , k | (true , q ) , l
    = ∣ inr (λ y → case absurd y (ap fst k) (ap fst l) of λ ()) ∣
      where
      fF≡fT : fst (f F) ≡ fst (f T)
      fF≡fT = ap (λ Q → fst (f Q)) F≡T

      absurd : A → (fst (f F) ≡ false) → (fst (f T) ≡ true) → false ≡ true
      absurd y ff ft = subst2 _≡_ ff ft fF≡fT
  ...| (true , p ) , _ | (false , q ) , _
    = ∥∥-rec (∥∥-isProp _) (λ z → +-elim z (λ ()) (λ a → in-left a)) p
  ...| (true , p ) , _ | (true , q ) , _
    = ∥∥-rec (∥∥-isProp _) (λ z → +-elim z (λ ()) (λ a → in-left a)) p

  -- proof of diaconescu

  Diaconescu : isProp A → PAC → A ∨ (¬ A)
  Diaconescu prop ac = ∥∥-rec (∥∥-isProp _) dec (ac (λ Q → snd Q))
