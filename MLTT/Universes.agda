{-# OPTIONS --without-K --exact-split --safe #-}

module MLTT.Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe  -- We speak of universes rather than of levels.
          ; lzero to U₀       -- Our first universe is called 𝓤₀
          ; lsuc to _⁺         -- The universe after 𝓤 is 𝓤 ⁺
          ; Setω to Uω        -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
          )
 using    (_⊔_)               -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁

Type = λ ℓ → Set ℓ
