module Data.Biconditional.BiconditionalTheorems where

open import Basics.Admit

open import Data.Biconditional.Biconditional


-- biconditional is an equivalence

⇔-refl : ∀ {l}{A : Set l} → A ⇔ A
⇔-refl = admit

⇔-sym : ∀ {l l'}{A : Set l}{B : Set l'} → A ⇔ B → B ⇔ A
⇔-sym = admit

⇔-trans : ∀ {l l' l''}{A : Set l}{B : Set l'}{C : Set l''} →
          A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans = admit
