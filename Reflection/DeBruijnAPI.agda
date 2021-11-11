module Reflection.DeBruijnAPI where

open import Algebra.Applicative.Applicative
open import Algebra.Functor.Functor
open import Algebra.Traversable.Traversable

open import Data.Bool.Bool
open import Data.Function.Function
open import Data.List.List
open import Data.Maybe.Maybe
open import Data.Nat.Nat
open import Data.Nat.Le
open import Data.Product.Product
open import Data.Vec.Vec
open import Data.String.String

open import Reflection.API

record DeBruijn {a} (A : Set a) : Set a where
  field
    strengthenFrom : (from n : ℕ) → A → Maybe A
    weakenFrom     : (from n : ℕ) → A → A

  strengthen : ℕ → A → Maybe A
  strengthen 0 = just
  strengthen n = strengthenFrom 0 n

  weaken : ℕ → A → A
  weaken zero = id
  weaken n    = weakenFrom 0 n

open DeBruijn {{...}} public

private
  Str : Set → Set
  Str A = ℕ → ℕ → A → Maybe A

  strVar : Str ℕ
  strVar lo n x = if      x <? lo     then just x
                  else if x <? (lo + n) then nothing
                  else                just (x - n)

  strArgs    : Str (List (Arg Term))
  strArg     : Str (Arg Term)
  strSort    : Str Sort
  strClauses : Str (List Clause)
  strClause  : Str Clause
  strAbsTerm : Str (Abs Term)
  strAbsType : Str (Abs Type)

  strTerm : Str Term
  strTerm lo n (var x args)  = var <$> strVar lo n x <*> strArgs lo n args
  strTerm lo n (con c args)  = con c <$> strArgs lo n args
  strTerm lo n (def f args)  = def f <$> strArgs lo n args
  strTerm lo n (meta x args) = meta x <$> strArgs lo n args
  strTerm lo n (lam v t)     = lam v <$> strAbsTerm lo n t
  strTerm lo n (pi a b)      = pi    <$> strArg lo n a <*> strAbsType lo n b
  strTerm lo n (agda-sort s) = agda-sort <$> strSort lo n s
  strTerm lo n (lit l)       = just (lit l)
  strTerm lo n (pat-lam _ _) = just unknown -- not necessary...
  strTerm lo n unknown       = just unknown

  strAbsTerm lo n (abs s t)  = abs s <$> strTerm (suc lo) n t
  strAbsType lo n (abs s t)  = abs s <$> strTerm (suc lo) n t

  strArgs    lo n []         = just []
  strArgs    lo n (x ∷ args) = _∷_   <$> strArg  lo n x <*> strArgs lo n args
  strArg     lo n (arg i v)  = arg i <$> strTerm lo n v
  strSort    lo n (set t)    = set   <$> strTerm lo n t
  strSort    lo n (lit l)    = just (lit l)
  strSort    lo n (prop t)   = prop <$> strTerm lo n t
  strSort    lo n (propLit t)= just (propLit t)
  strSort    lo n (inf l)    = just (inf l)
  strSort    lo n unknown    = just unknown

  strClauses lo k [] = just []
  strClauses lo k (c ∷ cs) = _∷_ <$> strClause lo k c <*> strClauses lo k cs

  strClause lo k (clause tel ps b)      = clause tel ps <$> strTerm (lo + length tel) k b
  strClause lo k (absurd-clause tel ps) = just (absurd-clause tel ps)

  strPat    : Str Pattern
  strPatArg : Str (Arg Pattern)
  strPats   : Str (List (Arg Pattern))

  strPat    lo k (con c ps) = con c <$> strPats lo k ps
  strPat    lo k (dot t)    = dot <$> strTerm lo k t
  strPat    lo k (var x)    = var <$> strVar lo k x
  strPat    lo k (lit l)    = pure (lit l)
  strPat    lo k (proj f)   = pure (proj f)
  strPat    lo k (absurd x) = absurd <$> strVar lo k x
  strPatArg lo k (arg i p)  = arg i <$> strPat lo k p
  strPats   lo k []         = pure []
  strPats   lo k (p ∷ ps)   = _∷_ <$> strPatArg lo k p <*> strPats lo k ps


private
  Wk : Set → Set
  Wk A = ℕ → ℕ → A → A

  wkVar : Wk ℕ
  wkVar lo k x = if x <? lo then x else x + k

  wkArgs    : Wk (List (Arg Term))
  wkArg     : Wk (Arg Term)
  wkSort    : Wk Sort
  wkClauses : Wk (List Clause)
  wkClause  : Wk Clause
  wkAbsTerm : Wk (Abs Term)

  wk : Wk Term
  wk lo k (var x args)  = var (wkVar lo k x) (wkArgs lo k args)
  wk lo k (con c args)  = con c (wkArgs lo k args)
  wk lo k (def f args)  = def f (wkArgs lo k args)
  wk lo k (meta x args) = meta x (wkArgs lo k args)
  wk lo k (lam v t)     = lam v (wkAbsTerm lo k t)
  wk lo k (pi a b)      = pi (wkArg lo k a) (wkAbsTerm lo k b)
  wk lo k (agda-sort s) = agda-sort (wkSort lo k s)
  wk lo k (lit l)       = lit l
  wk lo k (pat-lam cs args) = pat-lam (wkClauses lo k cs) (wkArgs lo k args)
  wk lo k unknown       = unknown


  wkAbsTerm lo k (abs s t)   = abs s (wk (suc lo) k t)
  wkArgs    lo k []          = []
  wkArgs    lo k (x ∷ args)  = wkArg lo k x ∷ wkArgs lo k args
  wkArg     lo k (arg i v)   = arg i (wk lo k v)
  wkSort    lo k (set t)     = set (wk lo k t)
  wkSort    lo k (lit n)     = lit n
  wkSort    lo k (prop t)    = prop (wk lo k t)
  wkSort    lo k (propLit n) = propLit n
  wkSort    lo k (inf n)     = inf n
  wkSort    lo k unknown     = unknown

  wkClauses lo k [] = []
  wkClauses lo k (c ∷ cs) = wkClause lo k c ∷ wkClauses lo k cs

  wkClause lo k (clause tel ps b)      = clause tel ps (wk (lo + length tel) k b)
  wkClause lo k (absurd-clause tel ps) = absurd-clause tel ps

  wkPat    : Wk Pattern
  wkPatArg : Wk (Arg Pattern)
  wkPats   : Wk (List (Arg Pattern))

  wkPat    lo k (con c ps) = con c (wkPats lo k ps)
  wkPat    lo k (dot t)    = dot (wk lo k t)
  wkPat    lo k (var x)    = var (wkVar lo k x)
  wkPat    lo k (lit l)    = lit l
  wkPat    lo k (proj f)   = proj f
  wkPat    lo k (absurd x) = absurd (wkVar lo k x)
  wkPatArg lo k (arg i p)  = arg i (wkPat lo k p)
  wkPats   lo k []         = []
  wkPats   lo k (p ∷ ps)   = wkPatArg lo k p ∷ wkPats lo k ps

DeBruijnTraversable : ∀ {a} {F : Set a → Set a} {{_ : Traversable F}}
                        {A : Set a} {{_ : DeBruijn A}} → DeBruijn (F A)
strengthenFrom {{DeBruijnTraversable}} lo k = traverse (strengthenFrom lo k)
weakenFrom     {{DeBruijnTraversable}} lo k = fmap     (weakenFrom lo k)

instance
  DeBruijnNat : DeBruijn ℕ
  strengthenFrom {{DeBruijnNat}} = strVar
  weakenFrom     {{DeBruijnNat}} = wkVar

  DeBruijnTerm : DeBruijn Term
  strengthenFrom {{DeBruijnTerm}} = strTerm
  weakenFrom     {{DeBruijnTerm}} = wk

  DeBruijnPattern : DeBruijn Pattern
  strengthenFrom {{DeBruijnPattern}} = strPat
  weakenFrom     {{DeBruijnPattern}} = wkPat

  DeBruijnList : ∀ {a} {A : Set a} {{_ : DeBruijn A}} → DeBruijn (List A)
  DeBruijnList = DeBruijnTraversable

  DeBruijnVec : ∀ {a} {A : Set a} {{_ : DeBruijn A}} {n : ℕ} → DeBruijn (Vec A n)
  DeBruijnVec = DeBruijnTraversable

  DeBruijnMaybe : {A : Set} {{_ : DeBruijn A}} → DeBruijn (Maybe A)
  DeBruijnMaybe = DeBruijnTraversable

  DeBruijnString : DeBruijn String
  strengthenFrom {{DeBruijnString}} _ _ = just
  weakenFrom     {{DeBruijnString}} _ _ = id
