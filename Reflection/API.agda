module Reflection.API where

open import Reflection.Core renaming ( primShowQName     to showName
                                     ; primQNameEquality to eqName
                                     ; primQNameLess     to lessName
                                     ) public
