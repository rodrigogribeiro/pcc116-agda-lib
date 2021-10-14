module Language.Data.Data where

open import Basics.Admit

open import Data.Bool.Bool
open import Data.Char.Char
open import Data.Empty.Empty
open import Data.Function.Function
open import Data.List.List hiding (foldl)
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Product.Product
open import Data.Sigma.Sigma renaming (_,_ to _,,_)
open import Data.Sum.Sum
open import Data.Unit.Unit
open import Data.Vec.Vec

-- codes for types

data Code : Set where
  BIT  : Code
  CHAR : Code
  NAT  : Code
  VEC  : Code → ℕ → Code


-- universe interpretation

data Bit : Set where
  O I : Bit

el : Code → Set
el BIT  = Bit
el CHAR = Char
el NAT  = ℕ
el (VEC c n) = Vec (el c) n


-- generic parser for types

readNat : Vec Bit 8 → ℕ
readNat bs = foldl step 0 bs
  where
    step : ℕ → Bit → ℕ
    step ac I = ac * 10 + 1
    step ac O = ac * 10

readChar : Vec Bit 8 → Char
readChar = ℕtoChar ∘ readNat

read : {c : Code} → List Bit → Maybe (el c × List Bit)

readVec : ∀ (n : ℕ)(c : Code) →
            List Bit          →
            Maybe (Vec (el c) n × List Bit)
readVec zero c bs = just ([] , bs)
readVec (suc n) c bs with read {c} bs
... | nothing = nothing
... | just (v , bs') with readVec n c bs'
...    | nothing = nothing
...    | just (vs , bs1) = just (v ∷ vs , bs1)


read {BIT} [] = nothing
read {BIT} (b ∷ bs) = just (b , bs)
read {CHAR} (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs)
  = just ( readChar (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ [])
         , bs
         )
read {CHAR} _ = nothing
read {NAT} (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ bs)
  = just ( readNat (b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ b₈ ∷ [])
         , bs
         )
read {NAT} _ = nothing
read {VEC c n} bs = readVec n c bs

-- file format DSL syntax and semantics

data File : Set
⟦_⟧ : File → Set

data File where
  Bad  : File
  End  : File
  Base : Code → File
  Plus : File → File → File
  Skip : File → File → File
  Read : (f : File) → (⟦ f ⟧ → File) → File

⟦ Bad ⟧ = ⊥
⟦ End ⟧ = ⊤
⟦ Base x ⟧ = el x
⟦ Plus f f₁ ⟧ = ⟦ f ⟧ ⊎ ⟦ f₁ ⟧
⟦ Skip f f₁ ⟧ = ⟦ f₁ ⟧
⟦ Read f x ⟧ = Σ ⟦ f ⟧ (λ y → ⟦ x y ⟧ )

-- DSL combinators

char : Char → File
char c = Read (Base CHAR)
              (λ c' → if c ≟ c'
                       then End
                       else Bad)

satisfy : (f : File) → (⟦ f ⟧ → Bool) → File
satisfy f p
  = Read f (λ x → if p x then End else Bad)

infixl 1 _>>=_ _>>_

_>>_ : File → File → File
f >> f' = Skip f f'

_>>=_ : (f : File) → (⟦ f ⟧ → File) → File
f >>= g = Read f g


-- generic file parser

parser : (f : File) → List Bit → Maybe (⟦ f ⟧ × List Bit)
parser Bad bs = nothing
parser End bs = just (tt , bs)
parser (Base x) bs = read {x} bs
parser (Plus f f₁) bs with parser f bs
...| just (v , bs') = just (inj₁ v , bs')
...| nothing with parser f₁ bs
...    | just (v' , bs') = just (inj₂ v' , bs')
...    | nothing = nothing
parser (Skip f f₁) bs = parser f₁ bs
parser (Read f x) bs with parser f bs
...| nothing = nothing
...| just (x₁ , cs) with parser (x x₁) cs
...    | nothing = nothing
...    | just (r , cs') = just ((x₁ ,, r) , cs')


-- EXERCÍCIO: implement generic printer

print : (f : File) → ⟦ f ⟧ → List Bit
print = admit


-- Examples

module Example where

nat : File
nat = Base NAT

vec : ℕ → ℕ → File
vec n m = Base (VEC (VEC BIT n) m)

pbm : File
pbm = do
       char 'P'
       char '4'
       char ' '
       n ← nat
       char ' '
       m ← nat
       char '\n'
       bs ← vec n m
       End
