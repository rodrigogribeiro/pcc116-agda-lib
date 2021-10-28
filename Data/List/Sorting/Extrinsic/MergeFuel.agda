open import Prelude.Classes

module Data.List.Sorting.Extrinsic.MergeFuel {A : Set}{{_ : Compare A}} where

open import Data.List.List    hiding (map)
open import Data.Maybe.Maybe
open import Data.Nat.Nat

merge-fuel : ℕ → List A → List A → Maybe (List A)
merge-fuel zero      xs       ys       = nothing
merge-fuel (suc gas) []       ys       = just ys
merge-fuel (suc gas) (x ∷ xs) []       = just (x ∷ xs)
merge-fuel (suc gas) (x ∷ xs) (y ∷ ys) with compare x y
...| less    = map (x ∷_) (merge-fuel gas xs (y ∷ ys))
...| equal   = map (y ∷_) (merge-fuel gas (x ∷ xs) ys)
...| greater = map (y ∷_) (merge-fuel gas (x ∷ xs) ys)
