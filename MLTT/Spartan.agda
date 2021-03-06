{-# OPTIONS --without-K --exact-split #-}

module MLTT.Spartan where

open import MLTT.Universes

variable U V W T : Universe

module Unit where
-- unit type

  data š : Type Uā where
    ā : š


  -- induction principle

  š-induction : (P : š ā Type U) ā P ā ā (x : š) ā P x
  š-induction P p ā = p

  -- recursion principle

  š-recursion : (B : Type U) ā B ā š ā B
  š-recursion B b x = š-induction (Ī» _ ā B) b x

  -- terminal object

  !šā² : (A : Type U) ā A ā š
  !šā² A x = ā

  !š : {A : Type U} ā A ā š
  !š x = ā

module Empty where

  data š : Type Uā where

  -- induction principle

  š-induction : (A : š ā Type U) ā (x : š) ā A x
  š-induction A ()

  -- recursion principle

  š-recursion : (A : Type U) ā š ā A
  š-recursion A a = š-induction (Ī» _ ā A) a

  !š : (A : Type U) ā š ā A
  !š = š-recursion

  -- negation definition

  is-empty : Type U ā Type U
  is-empty A = A ā š

  Ā¬_ : Type U ā Type U
  Ā¬ A = A ā š

module Natural where

  data ā : Type Uā where
    zero : ā
    suc  : ā ā ā

  {-# BUILTIN NATURAL ā #-}

  -- induction principle

  ā-induction : (P : ā ā Type U) ā
                P 0               ā
                ((n : ā) ā P n ā P (suc n)) ā
                (n : ā) ā P n
  ā-induction P base IH zero = base
  ā-induction P base IH (suc n) = IH n (ā-induction P base IH n)


  -- recursion principle

  ā-recursion : (A : Type U)  ā
                A             ā
                (ā ā A ā A) ā
                ā             ā
                A
  ā-recursion A = ā-induction (Ī» _ ā A)

  -- iteration

  ā-iteration : (A : Type U) ā
                A            ā
                (A ā A)     ā
                ā            ā
                A
  ā-iteration A a f = ā-recursion A a (Ī» _ y ā  f y)


-- ordering on ā

module ā-order where
  open Unit
  open Empty
  open Natural

  _ā¤_ : ā ā ā ā Type Uā
  0     ā¤ y     = š
  suc _ ā¤ zero  = š
  suc x ā¤ suc y = x ā¤ y

  _ā„_ : ā ā ā ā Type Uā
  x ā„ y = y ā¤ x


-- disjoint union: sum types

module Sum where

  infixl 4 _+_

  data _+_ (A : Type U)(B : Type V)  :  Type (U ā V) where
    inl : A ā A + B
    inr : B ā A + B

  -- induction principle

  +-induction : {A : Type U}{B : Type V}(P : A + B ā Type W) ā
                ((a : A) ā P (inl a))                        ā
                ((b : B) ā P (inr b))                        ā
                (z : A + B) ā P z
  +-induction P f g (inl a) = f a
  +-induction P f g (inr b) = g b

  -- recursion

  +-recursion : {A : Type U}{B : Type V}{C : Type W} ā
                (A ā C)                             ā
                (B ā C)                             ā
                (A + B) ā C
  +-recursion {C = C} = +-induction (Ī» _ ā C)


-- two point type: booleans

module Two where

  open Sum
  open Unit

  š : Type Uā
  š = š + š

  -- definition of constants

  pattern false = inl ā
  pattern true  = inr ā

  -- induction

  š-induction : (P : š ā Type U) ā P false ā P true ā (n : š) ā P n
  š-induction P Pfalse Ptrue false = Pfalse
  š-induction P Pfalse Ptrue true  = Ptrue

-- Dependent products: Ī£ types

module Sigma where


  record Ī£ {A : Type U}(B : A ā Type V) : Type (U ā V) where
    constructor _,_
    field
      fst : A
      snd : B fst

  -- induction principle

  Ī£-induction : {A : Type U}{B : A ā Type V}{P : Ī£ B ā Type W} ā
                ((a : A) ā (b : B a) ā P (a , b))                ā
                ((a , b) : Ī£ B)     ā P (a , b)
  Ī£-induction g (a , b) = g a b


  -- cartesian product

  _Ć_ : Type U ā Type V ā Type (U ā V)
  A Ć B = Ī£ {A = A} (Ī» _ ā B)


-- pi types

module Pi where


Ī  : {A : Type U}(B : A ā Type V) ā Type (U ā V)
Ī  {A = A} B = (x : A) ā B x

_ā_ : {A : Type U}{B : Type V}{C : B ā Type W} ā
      ((b : B) ā C b)                          ā
      (f : A ā B)                              ā
      (a : A) ā C (f a)
g ā f = Ī» a ā g (f a)


-- identity type

module Identity where

  data Id {U}(A : Type U) : A ā A ā Type U where
    refl : (x : A) ā Id A x x

  infix 4 _ā”_

  _ā”_ : {A : Type U} ā A ā A ā Type U
  x ā” y = Id _ x y

  -- induction

  š : (A : Type U)(P : (x y : A) ā xĀ ā” y ā Type V) ā
      ((x : A) ā P x x (refl x))                    ā
      (x y : A)(p : x ā” y) ā P x y p
  š A P f x x (refl x) = f x

  -- equality transport

  transport : {A : Type U}(P : A ā Type V){x y : A} ā
              x ā” y ā P x ā P y
  transport P (refl x) px = px

  -- composition of identifications

  lhs : {A : Type U}{x y : A} ā x ā” y ā A
  lhs {x = x} _ = x

  rhs : {A : Type U}{x y : A} ā x ā” y ā A
  rhs {y = y} _ = y

  _ā_ : {A : Type U}{x y z : A} ā x ā” y ā y ā” z ā x ā” z
  xy ā yz = transport (lhs xy ā”_) yz xy

  -- mixfix operators for identity type

  _ā”āØ_ā©_ : {A : Type U}(x : A){y z : A} ā x ā” y ā y ā” z ā x ā” z
  x ā”āØ xy ā© yz = xy ā yz

  _ā : {A : Type U}(x : A) ā x ā” x
  x ā = refl x

  _ā»Ā¹ : {A : Type U}{x y : A} ā x ā” y ā y ā” x
  xy ā»Ā¹ = transport (_ā” lhs xy) xy (refl (lhs xy))

  -- congruence

  ap : {A : Type U}{B : Type V}(f : A ā B){x y : A} ā x ā” y ā f x ā” f y
  ap f {x}{y} xy = transport (Ī» _ ā f x ā” f _) xy (refl (f x))

  -- pointwise equality of functions

  _~_ : {A : Type U}{B : A ā Type V} ā Ī  B ā Ī  B ā Type (U ā V)
  f ~ g = (x : _) ā f x ā” g x

  -- negation

  open Empty

  Ā¬Ā¬ : Type U ā Type U
  Ā¬Ā¬ A = Ā¬ (Ā¬ A)

  Ā¬Ā¬Ā¬ : Type U ā Type U
  Ā¬Ā¬Ā¬ A = Ā¬ (Ā¬ (Ā¬ A))

  -- double negation validity

  dni : (A : Type U) ā A ā Ā¬Ā¬ A
  dni A a u = u a

  -- contrapositiva

  contrapositive : {A : Type U}{B : Type V} ā (A ā B) ā (Ā¬ B ā Ā¬ A)
  contrapositive f nb a = nb (f a)

  -- definition of logical equivalence

  open Sigma

  infix 4 _ā_

  _ā_ : Type U ā Type V ā Type (U ā V)
  A ā B = (A ā B) Ć (B ā A)


  -- absurdity equivalence

  absurdityĀ³-absurdity : {A : Type U} ā Ā¬Ā¬Ā¬ A ā Ā¬ A
  absurdityĀ³-absurdity {A = A} = first , second
    where
      first : (Ā¬Ā¬Ā¬ A) ā Ā¬ A
      first = contrapositive (dni A)

      second : Ā¬ A ā Ā¬Ā¬Ā¬ A
      second = dni (Ā¬ A)

  -- inequality

  _ā¢_ : {A : Type U} ā A ā A ā Type U
  x ā¢ y = Ā¬ (x ā” y)

  ā¢-sym : {A : Type U}{x y : A} ā x ā¢ y ā y ā¢ x
  ā¢-sym {x = x}{y = y} xā¢y = Ī» (p : y ā” x) ā xā¢y (p ā»Ā¹)

  IdāFun : {A B : Type U}ā A ā” B ā A ā B
  IdāFun (refl A) = Ī» (x : A) ā x

  -- a simple property

  open Unit
  open Empty
  open Two

  š-is-not-š : š ā¢ š
  š-is-not-š p = IdāFun p ā

  true-is-not-false : true ā¢ false
  true-is-not-false p = š-is-not-š q
    where
      f : š ā Type Uā
      f false = š
      f true  = š

      q :  š ā” š
      q = ap f p

  -- decidable equality

  open Sum

  Dec : Type U ā Type U
  Dec A = A + Ā¬ A

  EqDec : Type U ā Type U
  EqDec A = (x y : A) ā Dec (x ā” y)

  -- two points type has a decidable equality

  š-EqDec : EqDec š
  š-EqDec false false = inl (refl (inl ā))
  š-EqDec false true  = inr (ā¢-sym true-is-not-false)
  š-EqDec true  false = inr true-is-not-false
  š-EqDec true  true  = inl (refl (inr ā))

  -- not false is true

  not-false-is-true : (n : š) ā n ā¢ false ā n ā” true
  not-false-is-true false f = !š (false ā” true) (f (refl false))
  not-false-is-true true  f = refl true


module Peano where

  open Unit
  open Empty
  open Natural
  open Sigma
  open Sum
  open Identity
  open ā-order

  suc-not-zero : (n : ā) ā suc n ā¢ 0
  suc-not-zero n p = š-is-not-š (g p)
    where
      f : ā ā Type Uā
      f zero    = š
      f (suc _) = š

      g : suc n ā” 0 ā š ā” š
      g = ap f


  pred : ā ā ā
  pred 0       = 0
  pred (suc x) = x

  suc-inv : {x y : ā} ā suc x ā” suc y ā x ā” y
  suc-inv = ap pred

  ā-EqDec : EqDec ā
  ā-EqDec zero zero = inl (refl zero)
  ā-EqDec zero (suc y) = inr (ā¢-sym (suc-not-zero y))
  ā-EqDec (suc x) zero = inr (suc-not-zero x)
  ā-EqDec (suc x) (suc y) = f (ā-EqDec x y)
    where
      f : Dec (x ā” y) ā Dec (suc x ā” suc y)
      f (inl p) = inl (ap suc p)
      f (inr q) = inr (q ā suc-inv)

  -- Exercises

  postulate admit : {A : Type U} ā A

  _ā_  _ā_ : ā ā ā ā ā

  x ā 0     = x
  x ā suc y = suc (x ā y)

  x ā 0     = 0
  x ā suc y = x ā x ā y

  infixl 20 _ā_
  infixl 21 _ā_

  -- Exercise 1.

  +-assoc : (x y z : ā) ā (x ā y) ā z ā” x ā (y ā z)
  +-assoc x y z = admit

  +-comm : (x y : ā) ā x ā y ā” y ā x
  +-comm = admit

  -- Exercise 2.

  _ā¼_ : ā ā ā ā Type Uā
  n ā¼ m  = Ī£ (Ī» (z : ā) ā n ā z ā” m)

  ā¤-gives-ā¼ : (x y : ā) ā x ā¤ y ā x ā¼ y
  ā¤-gives-ā¼ = admit

  ā¼-gives-ā¤ : (x y : ā) ā x ā¼ y ā x ā¤ y
  ā¼-gives-ā¤ = admit

  -- Exercise 3.

  _<_ : ā ā ā ā Type Uā
  x < y = suc x ā¤ y

  bounded-induction : (P : ā ā Type U)(k : ā)  ā
                      P k                       ā
                      ((n : ā) ā n < k ā P n) ā
                      (n : ā) ā n < suc k ā P n
  bounded-induction = admit
