{-# OPTIONS --without-K --exact-split --safe #-}

module MLTT.Universes where

open import Agda.Primitive public
 renaming (
            Level to Universe  -- We speak of universes rather than of levels.
          ; lzero to Uâ       -- Our first universe is called ð¤â
          ; lsuc to _âº         -- The universe after ð¤ is ð¤ âº
          ; SetÏ to UÏ        -- There is a universe ð¤Ï strictly above ð¤â, ð¤â, â¯ , ð¤â, â¯
          )
 using    (_â_)               -- Least upper bound of two universes, e.g. ð¤â â ð¤â is ð¤â

Type = Î» â â Set â
