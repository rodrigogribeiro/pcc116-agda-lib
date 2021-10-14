module Data.Tree.Tree where

open import Data.Maybe.Maybe
open import Data.Sum.Sum
open import Prelude.Classes
open import Relation.Equality.Propositional

data Tree (A : Set){{_ : Ord A}}(l u : [ A ]∞) : Set where
  leaf : {{ l≤u : l ≤ u }} → Tree A l u
  node : (v : A)         →
         Tree A l ⟨ v ⟩  →
         Tree A ⟨ v ⟩ u  →
         Tree A l u


module Search {{_ : Compare A}} where

  infix 4 _∈_

  data _∈_ {l u}(x : A) : (t : Tree A l u) → Set where
    here  : ∀ {t₁ t₂} → x ≡ y  → x ∈ node y t₁ t₂
    left  : ∀ {t₁ t₂} → x ∈ t₁ → x ∈ node y t₁ t₂
    right : ∀ {t₁ t₂} → x ∈ t₂ → x ∈ node y t₁ t₂

  ∈-inv : ∀ {l u x y}
            {t₁ : Tree A l ⟨ y ⟩}
            {t₂ : Tree A ⟨ y ⟩ u} →
            x ∈ node y t₁ t₂      →
            x ≡ y ⊎ x ∈ t₁ ⊎ x ∈ t₂
  ∈-inv (here x) = inj₁ x
  ∈-inv (left p) = inj₂ (inj₁ p)
  ∈-inv (right p) = inj₂ (inj₂ p)

  search : ∀ {l u}(x : A)(t : Tree A l u) → Maybe (x ∈ t)
  search x leaf = nothing
  search x (node v tl tr) with compare x v
  ...| equal   = just (here !)
  ...| less    = map left (search x tl)
  ...| greater = map right (search x tr)


open Search public

module Insert {{_ : Compare A}} where

  insert : ∀ {l u}(x : A)(t : Tree A l u)           →
             {{l≤x : l ≤ ⟨ x ⟩}}{{x≤u : ⟨ x ⟩ ≤ u}} →
             Tree A l u
  insert x leaf = node x leaf leaf
  insert x (node y tl tr) with compare x y
  ...| less    = node y (insert x tl) tr
  ...| equal   = node y tl tr
  ...| greater = node y tl (insert x tr)

open Insert public
