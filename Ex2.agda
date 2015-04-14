module Ex2 where

{-----------------------------------------------------------------------------
Name:
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
CS410 Exercise 2, due 5pm on Monday of Week 6 (3 November 2014)
NOTE: I am well aware that week 6 is quite busy with deadlines,
what with CS408-related obligations and so on. I'd much prefer
you did things to the best of your ability rather than on time,
so I would be sympathetic to requests for some flexibility.
Still, your best bet is to make an early start rather than a
late finish.
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
This exercise is based around extending Hutton's razor with Boolean
values and conditional expressions. By introducing a second value
type, we acquire the risk of type mismatch. The idea here is to
explore different approaches to managing that risk.
-----------------------------------------------------------------------------}

open import Ex1Prelude
open import Ex2Prelude

{- The extended Hutton's Razor syntax -}

data HExpIf : Set where
  num   : Nat -> HExpIf
  boo   : Two -> HExpIf
  _+++_ : HExpIf -> HExpIf -> HExpIf
  hif_then_else_ : HExpIf -> HExpIf -> HExpIf -> HExpIf

{- Note that an expression

   hif eb then ex1 else ex2

   makes sense only when
     * eb produces a Boolean value
     * ex1 and ex2 produce the same sort of value (numeric or Boolean)
-}

HValIf : Set
HValIf = Two /+/ Nat

{- We now have the risk of run time type errors. Let's introduce a type
for things which can go wrong. -}

data Error (E X : Set) : Set where
  ok    : X -> Error E X
  error : E -> Error E X

{- 2.1 Add a constructor to the following datatype for each different
   kind of run time error that can happen. (Come back to this exercise
   when you're writing the evaluator in 2.3.) Make these error reports
   as informative as you can.
-}

data EvalError : Set where
  BooleanExpectedInIf : EvalError
  CannotAddBoolean    : EvalError
  -- your constructors here

{- 2.2 Write a little piece of "glue code" to make it easier to manage
   errors. The idea is to combine error-prone process in *sequence*, where
   the second process can depend on the value produced by the first if it
   succeeds. The resulting process is, of course, also error-prone, failing
   as soon as either component fails.
-}

_>>=_ : {E S T : Set}
        -> Error E S          -- process which tries to get an S
        -> (S -> Error E T)   -- given an S, process which tries for a T
        -> Error E T          -- combined in sequence
ok x    >>= s2et = s2et x
error x >>= s2et = error x

{- 2.3 Implement an evaluator for HExpIf. Be sure to add only numbers and
   to branch only on Booleans. Report type mismatches as errors. You should
   use _>>=_ to help with the propagation of error messages.
-}

eval : HExpIf -> Error EvalError HValIf
eval (num x)    = ok (inr x)
eval (boo x)    = ok (inl x)
eval (e +++ e1) = eval e >>= (\ {(inr x) -> (eval e1 >>= (\ {(inr y) -> ok (inr (x + y))
                                                            ;(inl y) -> error CannotAddBoolean}))
                                ;(inl x) -> error CannotAddBoolean })                            
{--
-- a bit more verbose than the bind version but may communicate better
eval (e +++ e1) with eval e | eval e1
... | error err  | _          = error err
... | _          | error err  = error err
... | ok (inr x) | ok (inr y) = ok (inr (x + y))
... | ok (inl x) | _          = error CannotAddBoolean
... | _          | ok (inl x) = error CannotAddBoolean
--}
eval (hif num x then t_case else f_case)    = error BooleanExpectedInIf 
eval (hif boo x then t_case else f_case)    = if x then eval t_case else eval f_case
eval (hif hexpr then t_case else f_case)    = eval hexpr >>= (λ {(inl x) -> if x then eval t_case else eval f_case
                                                                ;(inr x) -> error BooleanExpectedInIf})

{- Note that the type of eval is not specific about whether the value
   expected is numeric or Boolean. It may help to introduce auxiliary
   definitions of error-prone processes which are "ok" only for the
   type that you really want.
-}

{- Next up, stack machine code, and its execution. -}

data HBCode : Set where
  PUSHN   : Nat -> HBCode
  PUSHB   : Two -> HBCode
  ADD     : HBCode
  _SEQ_   : HBCode -> HBCode -> HBCode
  _IFPOP_ : HBCode -> HBCode -> HBCode

{- The intended behaviour of (t IFPOP f) is as follows
  * pop the (we hope) Boolean value from top of stack
  * if it's tt, execute t, else execute f
  * whichever branch is executed, it gets the popped stack to start
-}

{- 2.4 Populate the type of possible execution errors and implement the
   execution behaviour of HBCode, operating on a stack represented as
   a list of HValIf values.
-}

data ExecError : Set where
  StackUnderflow : ExecError
  TypeErrorAdd  : ExecError
  TypeErrorIf   : ExecError
  -- your constructors here

exec : HBCode -> List HValIf -> Error ExecError (List HValIf)
exec (PUSHN x)                s   = ok (inr x :> s)
exec (PUSHB x)                s   = ok (inl x :> s)
exec ADD                      []  = error StackUnderflow
exec ADD               (x  :> []) = error StackUnderflow
exec ADD (inr x1 :> inr x2 :> s ) = ok (inr (x1 + x2) :> s)
exec ADD ( _     :> _      :> s ) = error TypeErrorAdd
exec (c1 SEQ c2)              s   = (exec c1 s) >>= (\ s -> exec c2 s) -- first execute c1 then c2
exec (c1 IFPOP c2)            []  = error StackUnderflow
exec (c1 IFPOP c2)  (inl x :> s)  = if x then (exec c1 s) else (exec c2 s)
exec (c1 IFPOP c2)  (inr x :> s)  = error TypeErrorIf

{- Next, we take a look at code generation and type safety. -}

data HTy : Set where  -- we have two types in HExpIf
  NUM BOOL : HTy

_=HTy=_ : HTy -> HTy -> Two   -- we can test if two types are equal
NUM  =HTy= NUM   = tt
NUM  =HTy= BOOL  = ff
BOOL =HTy= NUM   = ff
BOOL =HTy= BOOL  = tt

{- 2.5 Write a type-synthesizing compiler, computing both the HTy type and
   the HBCode executable for a given expression. Your compiler should
   give an informative error report if the expression it receives is
   ill typed. Your compiler should also ensure (at least informally) that
   the code produced will never trigger any execution errors.
-}

data CompileError : Set where
  ArithmaticError : HExpIf -> CompileError
  NatIsNotBool    : HExpIf -> CompileError
  InConsistentCases : HExpIf -> HExpIf -> CompileError
  -- your constructors here

compile : HExpIf -> Error CompileError (HTy /*/ HBCode)
compile (num x) = ok (NUM , PUSHN x)
compile (boo x) = ok (BOOL , PUSHB x)
compile (e1 +++ e2) = compile e1 >>= \
  {  (BOOL , c1)  -> error (ArithmaticError e1)
  ;  (NUM , c1)   -> (compile e2 >>= (\
                             { (BOOL , c2) -> error (ArithmaticError e2)
                             ; (NUM , c2) -> ok (NUM , (c1 SEQ c2) SEQ ADD)
                             }))
  }
compile (hif num x then e₁ else e₂)    = error (NatIsNotBool (num x))
compile (hif boo x then e₁ else e₂)    = if x then (compile e₁) else (compile e₂)
compile (hif test then t_case else f_case) = compile test >>= \
  { (BOOL , c) -> (compile t_case >>= (\
                  { (BOOL , bc1)  -> compile f_case >>= \
                                     { (BOOL , bc2) -> ok (BOOL , (c SEQ (bc1 IFPOP bc2)))
                                      ; (NUM , nc2) -> error (InConsistentCases t_case f_case) 
                                     }
                  ; (NUM , nc1)   -> compile f_case >>= \
                                     { (BOOL , bc2) -> error (InConsistentCases t_case f_case) 
                                      ; (NUM , nc2) -> ok (NUM , (c SEQ (nc1 IFPOP nc2)))
                                     }
                  }))
  ; (NUM , c)  -> error (NatIsNotBool test)
  }
-- TODO: use =HTy=



{- You have a little bit more room for creative problem-solving in what's
   left of the exercise. The plan is to build the type system into expressions
   and code, the same way we did with plain Hutton's Razor in class.
-}

{- If we *know* which HTy type we want, we can compute which Agda type we
   expect our value to take. -}

HVal : HTy -> Set
HVal NUM  = Nat
HVal BOOL = Two

{- 2.6 Finish the type of typed expressions. You should ensure that only
   well HTy-typed expressions can be constructed. -}

data THExpIf : HTy -> Set where
  val  : {t : HTy} -> HVal t -> THExpIf t
  add  : THExpIf NUM -> THExpIf NUM -> THExpIf NUM
  cond : {t : HTy} -> THExpIf BOOL -> THExpIf t -> THExpIf t -> THExpIf t
  -- you fill in addition and if-then-else

{- 2.7 Implement a type-safe evaluator. -}

teval : {t : HTy} -> THExpIf t -> HVal t
teval (val x)        = x
teval (add x x₁)     = (teval x) + (teval x₁)
teval (cond x x₁ x₂) = if (teval x) then (teval x₁) else (teval x₂)

{- 2.8 Implement a type checker. -}

data TypeError : Set where
  NotANat  : HExpIf -> TypeError
  NotABool : HExpIf -> TypeError
  -- your constructors here

tcheck : (t : HTy) -> HExpIf -> Error TypeError (THExpIf t)
tcheck NUM (num x)     = ok (val x)
tcheck NUM (boo x)     = error (NotANat (boo x))
tcheck NUM (e +++ e₁)  = (tcheck NUM e) >>= \ t -> (tcheck NUM e₁) >>= \ t2 -> ok (add t t2)
tcheck BOOL (e +++ e₁) = error (NotABool (e +++ e₁))
tcheck BOOL (num x)    = error (NotABool (num x))
tcheck BOOL (boo x)    = ok (val x)
tcheck t (hif e then e₁ else e₂) =
  (tcheck BOOL e) >>= \ b ->
  (tcheck t e₁) >>=  \ v1 ->
  (tcheck t e₂) >>= \ v2 -> ok (cond b v1 v2)



{- 2.9 Adapt the technique from Hutton.agda to give a type-safe underflow-free
   version of HBCode. You will need to think what is a good type to represent
   the "shape" of a stack: before, we just used Nat to represent the *height* of
   the stack, but now we must worry about types. See next question for a hint. 


All : {X : Set}            -- element type
      -> (X -> Set)        -- property of elements
      -> List X -> Set     -- property of whole lists
All P []         = One
All P (x :> xs)  = P x /*/ All P xs

{- If X = One, then List X is like a copy of Nat, and All is a bit like Vec -}

-}
data TVal : Set where
  tnum  : Nat -> TVal
  tbool : Two -> TVal 

data THBCode : HTy -> Set where
  TPUSHN   : Nat -> THBCode NUM
  TPUSHB   : Two -> THBCode BOOL
  TADD     : THBCode NUM
  _TSEQ_   : {t1 t2 : HTy} -> THBCode t1 -> THBCode t2 -> THBCode t2
  _TIFPOP_ : {t : HTy} -> THBCode t -> THBCode t -> THBCode t

{- 2.10 Implement the execution semantics for your code. You will need to think
   about how to represent a stack. The Ex2Prelude.agda file contains a very
   handy piece of kit for this purpose. You write the type, too. 

Stk : List One -> Set
Stk xs = All (\ _ -> Nat) xs


exec : {i j : List One} -> HCode i j -> Stk i -> Stk j
exec (PUSH x) s = x , s
exec ADD (x , (y , s)) = (y + x) , s
exec (h -SEQ- k) s = exec k (exec h s)

-}



--TStack : List One -> Set
--TStack xs = All (\ x -> TVal ) xs

--texec : {t : HTy} {n m : List One}-> THBCode t -> TStack n -> TStack m
texec : {t : HTy} {n m : List One}-> THBCode t -> TStack n -> TStack m
texec (TPUSHN x) s    = {!(tnum x) , s!}
texec (TPUSHB x) s    = {!!}
texec TADD s          = {!!}
texec (c TSEQ c₁) s   = {!!}
texec (c TIFPOP c₁) s = {!!}

-- your code here

{- 2.11 Write the compiler from well typed expressions to safe code. -}

tcompile : {t : HTy} -> THExpIf t -> {!!}
tcompile e = {!!}
