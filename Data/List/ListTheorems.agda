module Data.List.ListTheorems where

open import Algebra.Monoid.Monoid

open import Basics.Admit

open import Data.Biconditional.Biconditional
open import Data.Bool.Bool
open import Data.Function.Function
open import Data.List.List
open import Data.Maybe.Maybe
open import Data.Nat.Le
open import Data.Nat.Nat
open import Data.Nat.NatTheorems
open import Data.Product.Product
open import Data.Sigma.Sigma

open import Relation.Equality.Propositional

-- simple theorems of lists

length-++ : ∀ {a}{A : Set a}(xs ys : List A) →
            length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys       = refl
length-++ (x ∷ xs) ys
  = begin
      length ((x ∷ xs) ++ ys)
    ≡⟨⟩
      length (x ∷ (xs ++ ys))
    ≡⟨⟩
      suc (length (xs ++ ys))
    ≡⟨ cong suc (length-++ xs ys) ⟩
       suc (length xs + length ys)
    ≡⟨⟩
      length (x ∷ xs) + length ys
    ∎


map-++ : ∀ {a b}{A : Set a}{B : Set b}
           (f : A → B)(xs ys : List A) →
           map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys
    = begin
        map f ((x ∷ xs) ++ ys)
      ≡⟨⟩
        map f (x ∷ (xs ++ ys))
      ≡⟨⟩
        f x ∷ map f (xs ++ ys)
      ≡⟨ cong (f x ∷_) (map-++ f xs ys) ⟩
        f x ∷ (map f xs ++ map f ys)
      ≡⟨⟩
        map f (x ∷ xs) ++ map f ys
      ∎

map-∘ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
          {g : B → C}{f : A → B}(xs : List A) →
          (map g ∘ map f) xs ≡ map (g ∘ f) xs
map-∘ [] = refl
map-∘ {g = g}{f = f}(x ∷ xs)
    = begin
        (map g ∘ map f) (x ∷ xs)
      ≡⟨⟩
        map g (map f (x ∷ xs))
      ≡⟨⟩
        map g (f x ∷ (map f xs))
      ≡⟨⟩
        g (f x) ∷ map g (map f xs)
      ≡⟨⟩
        (g ∘ f) x ∷ ((map g ∘ map f) xs)
      ≡⟨ cong ((g ∘ f) x ∷_) (map-∘ xs)  ⟩
        (g ∘ f) x ∷ map (g ∘ f) xs
      ≡⟨⟩
        map (g ∘ f) (x ∷ xs)
      ∎

reverse-length : ∀ {a}{A : Set a}(xs : List A) →
                 length xs ≡ length (reverse xs)
reverse-length [] = refl
reverse-length (x ∷ xs)
    = begin
        length (x ∷ xs)
      ≡⟨⟩
        suc (length xs)
      ≡⟨ cong suc (reverse-length xs) ⟩
        suc (length (reverse xs))
      ≡⟨⟩
        1 + length (reverse xs)
      ≡⟨ +-comm 1 (length (reverse xs)) ⟩
        length (reverse xs) + 1
      ≡⟨⟩
        length (reverse xs) + length [ x ]
      ≡⟨ sym (length-++ (reverse xs) [ x ]) ⟩
        length (reverse xs ++ [ x ])
      ≡⟨⟩
        length (reverse (x ∷ xs))
      ∎

++-assoc : ∀ {a}{A : Set a}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc = admit

[]-++-right : ∀ {a}{A : Set a}(xs : List A) →
              xs ++ [] ≡ xs
[]-++-right [] = refl
[]-++-right (x ∷ xs)
    = begin
         (x ∷ xs) ++ []
      ≡⟨⟩
         x ∷ (xs ++ [])
      ≡⟨ cong (x ∷_) ([]-++-right xs) ⟩
         x ∷ xs
      ∎

reverse-++ : ∀ {a}{A : Set a}(xs ys : List A) →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys = sym ([]-++-right (reverse ys))
reverse-++ (x ∷ xs) ys
    = begin
        reverse ((x ∷ xs) ++ ys)
      ≡⟨⟩
        reverse (x ∷ (xs ++ ys))
      ≡⟨⟩
        reverse (xs ++ ys) ++ [ x ]
      ≡⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
        (reverse ys ++ reverse xs) ++ [ x ]
      ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
        reverse ys ++ (reverse xs ++ [ x ])
      ≡⟨⟩
        reverse ys ++ reverse (x ∷ xs)
      ∎

foldr-++ : ∀ {a}{A : Set a}
             {_⊕_ : A → A → A}{e : A} →
             IsMonoid _⊕_ e  →
             (xs ys : List A) →
             foldr _⊕_ e (xs ++ ys) ≡ foldr _⊕_ (foldr _⊕_ e ys) xs
foldr-++ M [] ys = refl
foldr-++ {_⊕_ = _⊕_}{e = e} M (x ∷ xs) ys
    = begin
        foldr _⊕_ e ((x ∷ xs) ++ ys)
      ≡⟨⟩
        foldr _⊕_ e (x ∷ (xs ++ ys))
      ≡⟨⟩
        x ⊕ (foldr _⊕_ e (xs ++ ys))
      ≡⟨ cong (x ⊕_) (foldr-++ M xs ys) ⟩
        x ⊕ (foldr _⊕_ (foldr _⊕_ e ys) xs)
      ≡⟨⟩
        foldr _⊕_ (foldr _⊕_ e ys) (x ∷ xs)
      ∎

filter-length : ∀ {a}{A : Set a}{p : A → Bool}(xs : List A) →
                length (filter p xs) ≤ length xs
filter-length [] = z≤n
filter-length {p = p}(x ∷ xs) with p x
...| true = s≤s (filter-length xs)
...| false = ≤-suc (filter-length xs)

-- Exercícios

unzip-zip : ∀ {a b}{A : Set a}{B : Set b}(xs : List A)(ys : List B) →
            length xs ≡ length ys → unzip (zip xs ys) ≡ (xs , ys)
unzip-zip = admit

foldr-map : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}{f : A → B}
              {_⊕_ : B → C → C}{v : C}(xs : List A) →
              (foldr _⊕_ v ∘ map f) xs ≡ foldr (_⊕_ ∘ f) v xs
foldr-map = admit

filter-&& : ∀ {a}{A : Set a}{P Q : A → Bool}(xs : List A) →
              (filter P ∘ filter Q) xs ≡ filter (λ x → P x && Q x) xs
filter-&& = admit



map-is-foldr : ∀ {a b}{A : Set a}{B : Set b}(f : A → B)(xs : List A) →
                 map f xs ≡ foldr (λ x ac → f x ∷ ac) [] xs
map-is-foldr = admit


foldr-fusion : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
               → (f : A → B → B)
               → (g : A → C → C)
               → (h : B → C)
               → {x : A}{y : B}
               → h (f x y) ≡ g x (h y)
               → (e : B) → ∀ xs
               → (h (foldr f e xs)) ≡ foldr g (h e) xs
foldr-fusion = admit


++-Monoid : ∀ {a}{A : Set a} → IsMonoid {A = List A} _++_ []
++-Monoid = admit

map-filter : ∀ {a b}{A : Set a}{B : Set b}(f : A → B)(p : B → Bool)(xs : List A) →
               (filter p ∘ map f) xs ≡ (map f ∘ filter (p ∘ f)) xs
map-filter = admit

nth-length-just : ∀ {a}{A : Set a}{n}(xs : List A) → n < length xs → ∃[ x ] (nth n xs ≡ just x)
nth-length-just = admit

nth-length-nothing : ∀ {a}{A : Set a}{n}(xs : List A) → length xs < n → nth n xs ≡ nothing
nth-length-nothing = admit

repeat-length : ∀ {a}{A : Set a}{x : A}(n : ℕ) → length (repeat x n) ≡ n
repeat-length = admit
