{-# OPTIONS --no-sized-types --no-guardedness
            --no-subtyping #-}

module Reflection.Core where

open import Basics.Level
open import Data.Bool.Bool
open import Data.Char.Char
open import Data.Float.Float
open import Data.List.List
open import Data.Nat.Nat
open import Data.Sigma.Sigma
open import Data.String.String
open import Data.Unit.Unit
open import Data.Word.Word

-- Names

postulate Name : Set
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

-- Fixity

data Associativity : Set where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : Set where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : Set where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

primitive
  primQNameFixity : Name → Fixity
  primQNameToWord64s : Name → Σ Word64 (λ _ → Word64)

-- Metavariables

postulate Meta : Set
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → ℕ

-- Arguments --

-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : Set where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′  #-}

-- Arguments can be relevant or irrelevant.
data Relevance : Set where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

-- Arguments also have a quantity.
data Quantity : Set where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

-- Relevance and quantity are combined into a modality.
data Modality : Set where
  modality : (r : Relevance) (q : Quantity) → Modality

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

data ArgInfo : Set where
  arg-info : (v : Visibility) (m : Modality) → ArgInfo

data Arg {a} (A : Set a) : Set a where
  arg : (i : ArgInfo) (x : A) → Arg A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

-- Name abstraction --

data Abs {a} (A : Set a) : Set a where
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

-- Literals --

data Literal : Set where
  nat    : (n : ℕ)    → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}

-- Terms and patterns --

data Term    : Set
data Sort    : Set
data Pattern : Set
data Clause  : Set
Type = Term

data Term where
  var       : (x : ℕ) (args : List (Arg Term)) → Term
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term
  lam       : (v : Visibility) (t : Abs Term) → Term
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
  pi        : (a : Arg Type) (b : Abs Type) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → List (Arg Term) → Term
  unknown   : Term

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : ℕ) → Sort
  prop    : (t : Term) → Sort
  propLit : (n : ℕ) → Sort
  inf     : (n : ℕ) → Sort
  unknown : Sort

data Pattern where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : (t : Term)    → Pattern
  var    : (x : ℕ)     → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : (x : ℕ)     → Pattern  -- absurd patterns counts as variables

data Clause where
  clause        : (tel : List (Σ String λ _ → Arg Type))
                  (ps : List (Arg Pattern))
                  (t : Term) → Clause
  absurd-clause : (tel : List (Σ String λ _ → Arg Type))
                  (ps : List (Arg Pattern)) → Clause

{-# BUILTIN AGDATERM      Term    #-}
{-# BUILTIN AGDASORT      Sort    #-}
{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDACLAUSE    Clause  #-}

{-# BUILTIN AGDATERMVAR         var       #-}
{-# BUILTIN AGDATERMCON         con       #-}
{-# BUILTIN AGDATERMDEF         def       #-}
{-# BUILTIN AGDATERMMETA        meta      #-}
{-# BUILTIN AGDATERMLAM         lam       #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
{-# BUILTIN AGDATERMPI          pi        #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit       #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTPROP        prop    #-}
{-# BUILTIN AGDASORTPROPLIT     propLit #-}
{-# BUILTIN AGDASORTINF         inf     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATDOT    dot     #-}
{-# BUILTIN AGDAPATVAR    var     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

{-# BUILTIN AGDACLAUSECLAUSE clause        #-}
{-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

-- Definitions --

data Definition : Set where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : ℕ) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

-- Errors --

data ErrorPart : Set where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  nameErr : Name → ErrorPart

{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

-- TC monad --

postulate
  TC               : ∀ {a} → Set a → Set a
  returnTC         : ∀ {a} {A : Set a} → A → TC A
  bindTC           : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC ⊤
  typeError        : ∀ {a} {A : Set a} → List ErrorPart → TC A
  inferType        : Term → TC Type
  checkType        : Term → Type → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : Set a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : Set a} → A → TC Term
  unquoteTC        : ∀ {a} {A : Set a} → Term → TC A
  quoteωTC         : ∀ {A : Setω} → A → TC Term
  getContext       : TC (List (Arg Type))
  extendContext    : ∀ {a} {A : Set a} → Arg Type → TC A → TC A
  inContext        : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → Type → TC ⊤
  declarePostulate : Arg Name → Type → TC ⊤
  defineFun        : Name → List Clause → TC ⊤
  getType          : Name → TC Type
  getDefinition    : Name → TC Definition
  blockOnMeta      : ∀ {a} {A : Set a} → Meta → TC A
  commitTC         : TC ⊤
  isMacro          : Name → TC Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A

  -- Makes the following primitives to reconstruct hidden arguments
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : Set a} → TC A → TC A

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → ℕ → List ErrorPart → TC ⊤

  -- Only allow reduction of specific definitions while executing the TC computation
  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A

  -- Don't allow reduction of specific definitions while executing the TC computation
  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : Set a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : Set a} → TC (Σ A λ _ → Bool) → TC A

{-# BUILTIN AGDATCM                           TC                         #-}
{-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
{-# BUILTIN AGDATCMBIND                       bindTC                     #-}
{-# BUILTIN AGDATCMUNIFY                      unify                      #-}
{-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
{-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
{-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
{-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
{-# BUILTIN AGDATCMBLOCKONMETA                blockOnMeta                #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMONLYREDUCEDEFS             onlyReduceDefs             #-}
{-# BUILTIN AGDATCMDONTREDUCEDEFS             dontReduceDefs             #-}
{-# BUILTIN AGDATCMWITHRECONSPARAMS           withReconstructed          #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}

newMeta : Type → TC Term
newMeta = checkType unknown

newMeta! : TC Term
newMeta! = newMeta unknown

set₀ : Type
set₀ = agda-sort (lit 0)

set! : Type
set! = agda-sort unknown
