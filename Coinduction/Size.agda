{-# OPTIONS --sized-types #-}

module Coinduction.Size where

open import Agda.Builtin.Size public using
  ( SizeUniv  --  sort SizeUniv
  ; Size      --  : SizeUniv
  ; Size<_    --  : Size → SizeUniv
  ; ↑_        --  : Size → Size
  ; _⊔ˢ_      --  : Size → Size → Size
  ; ∞         --  : Size
  )
