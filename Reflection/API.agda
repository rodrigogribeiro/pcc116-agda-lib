module Reflection.API where

open import Reflection.Core renaming ( primShowQName     to showName
                                     ; primQNameEquality to eqName
                                     ; primQNameLess     to lessName
                                     ; returnTC          to return
                                     ; bindTC            to _>>=_
                                     ) public

_>>_ : ∀ {A B : Set} → TC A → TC B → TC B
m >> m' = m >>= λ _ → m'
