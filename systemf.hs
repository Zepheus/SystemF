import Control.Exception
import Control.Monad
import           Test.HUnit
import Test.HUnit.Base (assertFailure)

type Symbol = String -- Use strings as symbol identifiers
-------------------------------------------------------
-- Types
-------------------------------------------------------

data Type = Bool |
            Nat |
            Fun Type Type | -- This is an arrow type of T1 -> T2
            -- System F:
            TVar Symbol |
            ForAll Type Type |
            -- List type |
            List Type |
            -- Error type
            TypeError String
            deriving (Eq)

instance Show Type where
  show Bool = "Bool"
  show Nat = "Nat"
  show (Fun a b) = "(" ++ show(a) ++ " → " ++ show(b) ++ ")"
  show (TVar s) = s
  show (List t) = "List " ++ show(t)
  show (ForAll s t) = "∀" ++ show(s) ++ ". " ++ show(t)
  show (TypeError s) = "TypeError:" ++ s

-- The environment is a collection of symbols linked with their type
type Environment = [(Symbol, Type)]

-- Type environment
type TEnvironment = [(Symbol, Type)]

-- Algebraic definition of the terms of our language.
data Term = TTrue  |
            TFalse |
            TIf Term  Term Term |
            Zero |
            Succ Term |
            Pred Term |
            IsZero Term |
            Add Term Term |
            Sub Term Term |
            Div Term Term |
            Even Term |
            Mul Term Term |
            Or Term Term |
            And Term Term |
            -- Simply typed lambda calculus:
            Var Symbol |
            Lambda Symbol Type Term | -- = Abs
            App Term Term |
            -- General recursion:
            Fix Term |
            -- System F
            TLambda Type Term | --Type = TVar
            TApp Term Type |
            -- List terms
            Nil Type |
            Cons Type Term Term |
            IsNil Type Term |
            Head Type Term |
            Tail Type Term
            deriving (Show,Eq)



-- Check whether a term is a numeric value
isNumeric Zero      = True
isNumeric (Succ t1) = isNumeric t1
isNumeric _         = False
-- Check whether a term is value
isValue TTrue  = True
isValue TFalse = True
-- List values:
isValue (Nil _) = True
isValue (Cons _ _ _) = True
--STLC values
isValue (Lambda _ _ _) = True -- Extra value type for lambda calculus
-- System F:
isValue (TLambda _ _) = True
-- Defaults:
isValue t      | isNumeric t = True
               | otherwise   = False

-- Simply typed lambda calculus, helper functions:
-- Extend the context with a new (Symbol, Type)
extend ctx s t = (s, t):ctx
getFromEnv = lookup -- Searching in the context
remove s v = filter (/= (Var s)) v

tremove s v = filter (/= (TVar s)) v

freevars::Term->[Term]
freevars (Var t) = [Var t]
freevars (Lambda s t body) = remove s (freevars body)
freevars (App fun arg) = freevars(fun)++freevars(arg)

-- Explicit freevars rules for old language!
freevars (Succ t) = freevars(t)
freevars (IsZero t) = freevars(t)
freevars (TIf t1 t2 t3) = freevars(t1)++freevars(t2)++freevars(t3)
freevars(Add t1 t2) = freevars(t1)++freevars(t2)
freevars (Sub t1 t2) = freevars(t1)++freevars(t2)
freevars (Mul t1 t2) = freevars(t1)++freevars(t2)
freevars (Div t1 t2) = freevars(t1)++freevars(t2)
freevars (Or t1 t2) = freevars(t1)++freevars(t2)
freevars (And t1 t2) = freevars(t1)++freevars(t2)
freevars (Even t) = freevars(t)
freevars (Fix t) = freevars(t)
-- Freevars for list:
freevars (Cons _ t1 t2) = freevars(t1) ++ freevars(t2)
freevars (IsNil _ t) = freevars(t)
freevars (Head _ t) = freevars(t)
freevars (Tail _ t) = freevars(t)
freevars _ = [] --  Normal terms have no free variables (e.g. zero)

-- Checks if a term variable is free
is_in_free::Symbol->[Term]->Bool
is_in_free s fvs = (>0) $ length $ filter (\(Var x)-> x == s) fvs

substitution::Symbol->Term->Term->Term
substitution x new (Var y) | x == y = new -- When it is the correct match
substitution x new (Var y) = Var y -- When x is not the same symbol
substitution x new (Lambda s t body) | x /= s && not (is_in_free s (freevars new)) = Lambda s t (substitution x new body)
substitution x new e@(Lambda s t body) = e -- Does not apply to bound checks, either not subs or already bound
substitution x new (App fun arg) = App (substitution x new fun) (substitution x new arg)
substitution x new (Succ t) = Succ (substitution x new t)
substitution x new (IsZero t) = IsZero (substitution x new t)
substitution x new (TIf t1 t2 t3) = TIf (substitution x new t1) (substitution x new t2) (substitution x new t3)
substitution x new (Add t1 t2) = Add (substitution x new t1) (substitution x new t2)
substitution x new (Sub t1 t2) = Sub (substitution x new t1) (substitution x new t2)
substitution x new (Mul t1 t2) = Mul (substitution x new t1) (substitution x new t2)
substitution x new (Div t1 t2) = Div (substitution x new t1) (substitution x new t2)
substitution x new (Or t1 t2) = Or (substitution x new t1) (substitution x new t2)
substitution x new (And t1 t2) = And (substitution x new t1) (substitution x new t2)
substitution x new (Even t) = Even (substitution x new t)
substitution x new (Fix t) = Fix (substitution x new t)
substitution x new (Pred t) = Pred (substitution x new t)
-- List substitutions
substitution x new (Cons t t1 t2) = Cons t (substitution x new t1) (substitution x new t2)
substitution x new (IsNil t t1) = IsNil t (substitution x new t1)
substitution x new (Head t t1) = Head t (substitution x new t1)
substitution x new (Tail t t1) = Tail t (substitution x new t1)

substitution _ _ t | isValue t = t -- value types simply return themselves (e.g. succ zero)

-- Free type variables (same as for the original lambda)
freetvars::Type->[Symbol]
freetvars (TVar s) = [s]
freetvars (ForAll (TVar s) t) = filter (/=s) (freetvars(t))
freetvars (Fun a b) = freetvars(a)++freetvars(b)
freetvars _ = []

is_in_freetvars s fvs = (>0) $ length $ filter (== s) fvs

-- Typechecker substitutions
typesubs::Symbol->Type->Type->Type
typesubs x new (ForAll (TVar s) t) | x /= s && (not (is_in_freetvars s (freetvars new))) = ForAll (TVar s) (typesubs x new t)
typesubs x new f@(ForAll s t) = f
typesubs x new (List t) = List (typesubs x new t)
typesubs x new (Fun a b) = Fun (typesubs x new a) (typesubs x new b)
typesubs x new (TVar s)
              | x == s = new
              | otherwise = TVar s
typesubs _ _ t = t -- all other types remain

-- Type substitutions
tsubstitution::Symbol->Type->Term->Term
tsubstitution x new (TLambda (TVar s) body) | x /= s && not (is_in_freetvars s (freetvars new)) = TLambda (TVar s) (tsubstitution x new body)
tsubstitution x new e@(TLambda (TVar s) body) = e
tsubstitution x new (Lambda v (TVar s) body) | s == x = Lambda v new (tsubstitution x new body) -- substitute type in lambda
tsubstitution x new (Lambda s v body) = Lambda s (typesubs x new v) (tsubstitution x new body)

-- Basic t-sub cases
tsubstitution x new (Var s) = Var s
tsubstitution x new (App fun arg) = App (tsubstitution x new fun) (tsubstitution x new arg)
tsubstitution x new (Succ t) = Succ (tsubstitution x new t)
tsubstitution x new (IsZero t) = IsZero (tsubstitution x new t)
tsubstitution x new (TIf t1 t2 t3) = TIf (tsubstitution x new t1) (tsubstitution x new t2) (tsubstitution x new t3)
tsubstitution x new (Add t1 t2) = Add (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (Sub t1 t2) = Sub (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (Mul t1 t2) = Mul (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (Div t1 t2) = Div (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (Or t1 t2) = Or (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (And t1 t2) = And (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (Even t) = Even (tsubstitution x new t)
tsubstitution x new (Fix t) = Fix (tsubstitution x new t)

-- List type substitutions
tsubstitution x new (Nil t) = Nil (typesubs x new t)
tsubstitution x new (Cons t t1 t2) = Cons (typesubs x new t) (tsubstitution x new t1) (tsubstitution x new t2)
tsubstitution x new (IsNil t t1) = IsNil (typesubs x new t) (tsubstitution x new t1)
tsubstitution x new (Head t t1) = Head (typesubs x new t) (tsubstitution x new t1)
tsubstitution x new (Tail t t1) = Tail (typesubs x new t) (tsubstitution x new t1)
tsubstitution _ _ t | isValue t = t

-- System F:
eval (TApp (TLambda (TVar s) body) arg) = tsubstitution s arg body --E-TAPP-TABS
eval (TApp f arg) | not (isValue f) = TApp f' arg --E-TAPP
                                    where f' = eval f

-- General recursion primitive
eval f@(Fix (Lambda s t body)) = f'
  where f' = substitution s f body -- E-FIXBETA
eval (Fix t) | not $ isValue t = Fix t' where
    t' = (eval t) -- E-FIX
eval (Fix _) = error "No abstraction given to fix."

-- List:
eval (Cons t v1 t2) | isValue v1 = Cons t v1 t2'
  where t2' = eval t2 -- E-CONS2
eval (Cons t t1 t2) = Cons t t1' t2
  where t1' = eval t1 --E-CONS1
eval (IsNil _ (Nil _)) = TTrue --E-ISNILNIL
eval (IsNil t1 (Cons t2 v1 v2)) | isValue v1 && isValue v2 = TFalse -- E-ISNILCONS
eval (IsNil t t1) = IsNil t t1'
  where t1' = eval t1 --E-ISNIL
eval (Head t1 (Cons t2 v1 v2)) | isValue v1 && isValue v2 = v1 --E-HEADCONS
eval (Head t t1) = Head t t1'
  where t1' = eval t1 --E-HEAD
eval (Tail t1 (Cons t2 v1 v2)) | isValue v1 && isValue v2 = v2 --E-TAILCONS
eval (Tail t t1) = Tail t t1'
  where t1' = eval t1 --E-TAIL

-- Simply typed lambda calculus:
eval (App (Lambda s t body) arg) | isValue arg = substitution s arg body --E-APPABS
eval (App f arg) | not (isValue f) = App f' arg --E-APP1
                                    where f' = eval f
eval (App f arg) | not (isValue arg) = App f arg' --E-APP2
                                    where arg' = eval arg

-- Old evaluators
eval (TIf TTrue  t2 t3) =  t2
eval (TIf TFalse t2 t3) =  t3
eval (TIf t1     t2 t3) = (TIf t1' t2 t3)
                          where t1' = eval t1

eval (Succ t1)          = (Succ t1')
                          where t1' = eval t1

eval (Pred Zero)        = Zero

eval (Pred (Succ t1))   | isNumeric t1 = t1

eval (Pred t1)          = (Pred t1')
                           where t1' = eval t1

eval (IsZero Zero)                      = TTrue
eval (IsZero (Succ t1)) | isNumeric t1  = TFalse
eval (IsZero t1)                        = (IsZero t1')
                                          where t1' = eval t1 -- congruentieregel

eval (Add Zero t1) = t1
eval (Add t1 t2) | isNumeric t1 && isNumeric t2   = Add (Pred t1) (Succ t2)
eval (Add t1 t2) | isNumeric t1                   = Add t1 (t2')
                                                    where t2' = eval t2
eval (Add t1 t2)                                  = Add t1' t2
                                                    where t1' = eval t1

eval (Sub t1 Zero)                                = t1
eval (Sub t1 t2) | isNumeric t1 && isNumeric t2   = Sub (Pred t1) (Pred t2)
eval (Sub t1 t2) | isNumeric t1                   = Sub t1 t2'
                                                    where t2' = eval t2
eval (Sub t1 t2)                                  = Sub t1' t2
                                                    where t1' = eval t1


eval (Mul Zero t1)                                      = Zero
eval (Mul t1 (Succ Zero))                               = t1
eval (Mul t1 (Succ t2)) | isNumeric t1 && isNumeric t2  = Add t1 (Mul t1 t2)
eval (Mul t1 t2) | isNumeric t1                         = Mul t1 t2'
                                                          where t2' = eval t2
eval (Mul t1 t2)                                        = Mul t1' t2
                                                          where t1' = eval t1


eval (Div _ Zero)                                       = error "Division by zero"
eval (Div Zero _)                                       = Zero
eval (Div t1 t2) | isNumeric t1 && isNumeric t2         = Succ (Div (Sub t1 t2) t2)
eval (Div t1 t2) | isNumeric t1                         = Div t1 t2'
                                                          where t2' = eval t2
eval (Div t1 t2)                                        = Div t1' t2
                                                          where t1' = eval t1


eval (Or TTrue _)                   = TTrue
eval (Or TFalse TTrue)              = TTrue
eval (Or TFalse TFalse)             = TFalse
eval (Or TFalse t2)                 = t2
eval (Or t1 t2)                     = Or t1' t2
                                      where t1' = eval t1

eval (And TTrue TTrue)              = TTrue
eval (And TFalse _)                 = TFalse
eval (And _ TFalse)                 = TFalse
eval (And t1 t2) | isValue t1       = And t1 t2'
                                      where t2' = eval t2
eval (And t1 t2)                    = And t1' t2
                                      where t1' = eval t1


eval (Even Zero)                            = TTrue
eval (Even (Succ Zero))                     = TFalse
eval (Even (Succ (Succ t1))) | isNumeric t1 = Even t1
eval (Even t1)                              = Even t1'
                                              where t1' = eval t1

-- if nothing else works we either have a bad term
-- or it is already a value
eval x                  = x

evalStar x | x == x'  && isValue x'  = x'
           | x == x'                 = error $ "Bad term: " ++ show x'
           | otherwise               = evalStar x'
             where x'   = eval x

searchTypeInEnv::Type->TEnvironment->Type
searchTypeInEnv (TVar s) tctx =
 case (getFromEnv s tctx) of
   Just t -> t
   Nothing -> TypeError "Unreferenced type variable"
searchTypeInEnv t _ = t -- All other types are the type itself

-- Typechecks
-- Two contexts are required: one for type variable bindings and one for term variable bindings
typeCheck::Environment->TEnvironment->Term->Type

-- Typechecks for System F
typeCheck ctx tctx (TLambda (TVar s) body) = ForAll (TVar s) (typeCheck ctx ((s, TVar s):tctx) body)
typeCheck ctx tctx (TApp t1 t2) =
    case t1' of
      ForAll (TVar s) t -> typesubs s t2 t
      _ -> TypeError ("Type application on non-type abstraction: " ++ show(t1'))
    where t1' = typeCheck ctx tctx t1

-- Typecheck for general recursion
typeCheck ctx tctx (Fix t) =
    case t' of
      Fun a b -> b
      _ -> TypeError "Invalid fix type. Expected arrow-type"
    where
      t' = typeCheck ctx tctx t

-- Typecheck for List
typeCheck ctx tctx (Nil t) | searchTypeInEnv t tctx == t = List t
typeCheck ctx tctx (Cons t1 t2 t3) | typeCheck ctx tctx t2 == searchTypeInEnv t1 tctx && typeCheck ctx tctx t3 == List (searchTypeInEnv t1 tctx) = List t1
typeCheck ctx tctx (Cons t1 t2 t3) = TypeError ("Cons body types do not match signature: " ++ show(t1) ++ ";" ++ show(typeCheck ctx tctx t2) ++ "; " ++ show(typeCheck ctx tctx t3))
typeCheck ctx tctx (IsNil t11 t12) | typeCheck ctx tctx t12 == (List t11) = Bool
typeCheck ctx tctx (IsNil t11 t12) = TypeError "IsNil t12 is not a List"
typeCheck ctx tctx (Head t11 t12) | typeCheck ctx tctx t12 == (List (searchTypeInEnv t11 tctx)) = t11
typeCheck ctx tctx (Head t11 t12) = TypeError "Head of list is not of correct type as in signature"
typeCheck ctx tctx (Tail t11 t12) | typeCheck ctx tctx t12 == (List (searchTypeInEnv t11 tctx)) = List t11
typeCheck ctx tctx (Tail t11 t12) = TypeError "Tail of list is not of correct type as in signature"

-- Typechecks simply typed
typeCheck ctx tctx (Var s) = case (getFromEnv s ctx) of
  Just t -> t
  Nothing -> TypeError "Unrefenced Variable used"

typeCheck ctx tctx (Lambda sym typ term) = Fun typ' (typeCheck (extend ctx sym typ) tctx term)
  where typ' = searchTypeInEnv typ tctx  -- Check if the type is in the type environment

typeCheck ctx tctx (App t1 t2) =
    case t1' of
        (Fun t1l t1r) | t1l == t2' -> t1r
        (Fun t1l _) -> TypeError ("Argument of application does not match abstraction: signature="
          ++ show(t1l) ++ "; argument: " ++ show(t2') ++ "; body: " ++ show(t2))-- Fails to match input type to body type
        _ -> TypeError "Body is not a function"
    where t1' = typeCheck ctx tctx t1
          t2' = typeCheck ctx tctx t2

typeCheck _ _ TTrue  = Bool
typeCheck _ _ TFalse = Bool
typeCheck ctx tctx (TIf t1 t2 t3) =
     if (type1 == Bool) && (type2 == type3) then
          type3
     else if (type1 /= Bool) then
          TypeError "If predicate not well typed"
     else
        TypeError ("If Left is not equally typed as right: left=" ++ show(type2) ++ "; right: " ++ show(type3))
     where type1 = typeCheck ctx tctx t1
           type2 = typeCheck ctx tctx t2
           type3 = typeCheck ctx tctx t3
typeCheck _ _ Zero = Nat
typeCheck ctx tctx (Succ t) | typeCheck ctx tctx t == Nat = Nat
typeCheck _ _ (Succ _) = TypeError "Succ expects Nat argument"
typeCheck ctx tctx (Pred t) | typeCheck ctx tctx t == Nat = Nat
typeCheck _ _ (Pred _) = TypeError "Pred expects Nat argument"
typeCheck ctx tctx (IsZero t) | typeCheck ctx tctx t == Nat = Bool
typeCheck _ _ (IsZero _) = TypeError "IsZero expects Nat argument"
typeCheck ctx tctx (Even t) | typeCheck ctx tctx t == Nat = Bool
typeCheck _ _ (Even _) = TypeError "Even expects Nat argument"

-- Arithmetic operations all assume Nat
typeCheck ctx tctx (Add t1 t2) | typeCheck ctx tctx t1 == Nat && typeCheck ctx tctx t2 == Nat = Nat
typeCheck ctx tctx (Sub t1 t2) | typeCheck ctx tctx t1 == Nat && typeCheck ctx tctx t2 == Nat = Nat
typeCheck ctx tctx (Mul t1 t2) | typeCheck ctx tctx t1 == Nat && typeCheck ctx tctx t2 == Nat = Nat
typeCheck ctx tctx (Div t1 t2) | typeCheck ctx tctx t1 == Nat && typeCheck ctx tctx t2 == Nat = Nat

-- Logical statements assume bool in both terms
typeCheck ctx tctx (Or t1 t2)  | typeCheck ctx tctx t1 == Bool && typeCheck ctx tctx t2 == Bool = Bool
                      | otherwise = TypeError "Or expects two arguments of type Bool"
typeCheck ctx tctx (And t1 t2) | typeCheck ctx tctx t1 == Bool && typeCheck ctx tctx t2 == Bool = Bool
                      | otherwise = TypeError "And expects two arguments of type Bool"

-- Helper function made to represent natural number in Term notation. (Written together with Matthias and Benjamin)
vt :: Int -> Term
vt 0 = Zero
vt i = (Succ (vt (i-1)))

ivt :: Term -> Int
ivt Zero = 0
ivt (Succ t) = 1 + (ivt t)

-- Helpers to assert on Type errors or exceptions
isError x = case x of
  TypeError _ -> True
  Fun x t -> isError x || isError t
  _ -> False

assertError msg f = assertBool msg (isError f)

assertException :: (Exception e, Eq e) => e -> IO a -> IO ()
assertException ex action =
    handleJust isWanted (const $ return ()) $ do
        action
        assertFailure $ "Expected exception: " ++ show ex
  where isWanted = guard . (== ex)

assertErrorMsg ex f = assertException (ErrorCall ex) $ evaluate f

test1 = TestCase  (assertEqual "IfFalse " (Succ Zero) (evalStar (TIf (IsZero (Succ (Pred (Pred Zero)))) Zero (Succ Zero))))
test2 = TestCase  (assertEqual "IfTrue"    Zero       (evalStar (TIf (IsZero (Pred (Pred Zero))) Zero (Succ Zero))))
test4 = TestCase  (assertEqual "IsNumericTrue" (True) (isNumeric (evalStar (Pred Zero))))
test5 = TestCase  (assertEqual "AddZeros" (Zero)      (evalStar (Add Zero Zero)))
test6 = TestCase  (assertEqual "AddValue" (vt 2)      (evalStar (Add (vt 2) Zero)))
test7 = TestCase  (assertEqual "AddValue" (vt 2)      (evalStar (Add Zero (vt 2))))
test8 = TestCase  (assertEqual "AddValues" (vt 5)     (evalStar (Add (vt 3) (vt 2))))
test9 = TestCase  (assertEqual "AddAddValues" (vt 5)  (evalStar (Add (vt 1) (Add (vt 2) (vt 2)))))
test10 = TestCase  (assertEqual "MulZero" (Zero)      (evalStar (Mul Zero (vt 2))))
test11 = TestCase  (assertEqual "MulOne" (vt 2)       (evalStar (Mul (vt 1) (vt 2))))
test12 = TestCase  (assertEqual "MulValues" (vt 20)   (evalStar (Mul (vt 5) (vt 4))))
test13 = TestCase  (assertEqual "MulMulValues" (vt 30)(evalStar (Mul (vt 5) (Mul (vt 2) (vt 3)))))
test14 = TestCase  (assertEqual "MulAddValues" (vt 25)(evalStar (Mul (vt 5) (Add (vt 2) (vt 3)))))
test15 = TestCase  (assertEqual "OrAndAnd" (TFalse)   (evalStar (And (And TTrue TFalse) (Or TFalse TTrue))))
test16 = TestCase  (assertEqual "OrAndAnd" (TTrue)   (evalStar (Or (And TTrue TFalse) (Or TFalse TTrue))))
test17 = TestCase  (assertEqual "SimpleOr" (TTrue)   (evalStar (Or TFalse (Or TFalse TTrue))))
test18 = TestCase  (assertEqual "SimpleSub" (Succ Zero)     (evalStar (Sub (Succ (Succ Zero)) (Succ Zero))))
test19 = TestCase  (assertEqual "SubZero" (vt 3)     (evalStar (Sub (vt 3) (Zero))))
test20 = TestCase  (assertEqual "SubNormal" (vt 7)     (evalStar (Sub (vt 10) (vt 3))))
test21 = TestCase  (assertEqual "DivSimpel" (vt 4)     (evalStar (Div (vt 20) (vt 5))))
test29 = TestCase  (assertEqual "EvenFalse" (TFalse)     (evalStar (Even (vt 5))))
test30 = TestCase  (assertEqual "EvenTrue" (TTrue)     (evalStar (Even (vt 6))))

-- Typechecks of old code
-- Helper method to typecheck starting with empty environments
typeCheckSimple x = typeCheck [] [] x

test3 = TestCase  (assertEqual "TTrueBool" (Bool)     (typeCheckSimple TTrue))
test23 = TestCase  (assertEqual "MulNat" (Nat)     (typeCheckSimple (Mul (vt 2) (vt 3))))
test24 = TestCase  (assertEqual "DivNat" (Nat)     (typeCheckSimple (Div (vt 20) (vt 4))))
test25 = TestCase  (assertEqual "SubNat" (Nat)     (typeCheckSimple (Sub (vt 3) (vt 2))))
test26 = TestCase  (assertEqual "AddNat" (Nat)     (typeCheckSimple (Add (vt 2) (vt 3))))
test27 = TestCase  (assertEqual "OrBool" (Bool)    (typeCheckSimple (Or (And TTrue TFalse) (Or TFalse TTrue))))
test28 = TestCase  (assertEqual "AddNat" (Nat)     (typeCheckSimple (Add (Sub (vt 5) (vt 3)) (vt 3))))
test31 = TestCase  (assertEqual "EvenType" (Bool)     (typeCheckSimple (Even (Add (vt 2) (vt 3)))))

-- Tests for Simply typed lambda calculus
-- Evaluation
test41 = TestCase (assertEqual "evalSuccLambda" (vt 3) (evalStar (App (Lambda "s" Nat (Succ (Var "s"))) (vt 2))))
test42 = TestCase (assertErrorMsg "Bad term: Succ (Var \"k\")" (evalStar (App (Lambda "s" Nat (Succ (Var "k"))) (vt 2))))
test43 = TestCase (assertEqual "evalEvenLambda" (TFalse) (evalStar (App (Lambda "s" Nat (IsZero (Succ (Var "s")))) (vt 0))))
test44 = TestCase (assertEqual "evalLambdaIf" (vt 1) (evalStar (App (Lambda "s" Bool (TIf (Var "s") (vt 1) (vt 2))) TTrue)))
test45 = TestCase (assertEqual "evalLambdaIfFalse" (vt 2) (evalStar (App (Lambda "s" Bool (TIf (Var "s") (vt 1) (vt 2))) TFalse)))

-- Typesystem
-- Typecheck helper method for simply typed lambda calculus without type variable bindings
typeCheckSLambda env x = typeCheck env [] x

test32 = TestCase (assertEqual "ContextLookup" (Nat) (typeCheckSLambda [("blah", Nat)] (Var "blah"))) -- Tests environment lookup
test33 = TestCase (assertError "Symbol not in environment" (typeCheckSimple (Var "blah"))) -- Empty environment should fail
test34 = TestCase (assertEqual "LambdaType" (Fun Nat Nat) (typeCheckSimple (Lambda "blah" Nat (vt 3))))
test35 = TestCase (assertEqual "LambdaType2" (Fun Bool Nat) (typeCheckSimple (Lambda "blah" Bool (vt 3))))
test36 = TestCase (assertEqual "AppType" (Bool) (typeCheckSimple (App (Lambda "s" Nat (TTrue)) (vt 2))))
test37 = TestCase (assertError "Type mismatch" (typeCheckSimple (App (Lambda "s" Bool (vt 2)) (vt 2))))
test38 = TestCase (assertEqual "AppType2" (Nat) (typeCheckSimple (App (Lambda "s" Nat (Succ (Var "s"))) (vt 2))))
test39 = TestCase (assertEqual "LambdaTypes" (Fun Nat Nat) (typeCheckSimple (Lambda "s" Nat (Succ (Var "s")))))
test40 = TestCase (assertError "Fun Bool Not well typed" (typeCheckSimple (Lambda "s" Bool (Succ (Var "s")))))
test46 = TestCase (assertError "WrongAbstractionApplication" (typeCheckSimple (App (Lambda "s" Bool (Even (Var "s"))) (vt 1))))
test47 = TestCase (assertError "WrongAbstraction" (typeCheckSimple (App (Lambda "s" Bool (Even (Var "s"))) TTrue)))

old_tests = [test1,test2,test3,test4,test5,test6,test7,test8,
                            test9,test10,test11,test12,test13,test14,test15,test16,test17,test18,
                            test19,test20,test21,test23,test24,test25,test26,test27,test28,test29,test30,test31,
                            test32, test33,test34,test35,test36,test37,test38,test39,test40,test41,test42,test43,
                            test44,test45,test46,test47]

-- Tests for System F:
fid = (TLambda (TVar "X") (Lambda "x" (TVar "X") (Var "x"))) -- Polymorphic Identity function

-- double function from TAPL p.344s
double = TLambda (TVar "X") (Lambda "f" (Fun (TVar "X") (TVar "X")) (Lambda "a" (TVar "X") (App (Var "f") (App (Var "f") (Var "a")))))
doubleNat = TApp double Nat
doubleNatArrowNat = TApp double (Fun Nat Nat)
doubleNatSucc x = App (App doubleNat (Lambda "x" Nat (Succ (Succ (Var "x"))))) x
quadruple = TLambda (TVar "Y") (App (TApp double (Fun (TVar "Y") (TVar "Y"))) (TApp double (TVar "Y")))

-- Test for nested lambda's
nestedLambdas = TLambda (TVar "X") (TLambda (TVar "Y") (Lambda "x" (TVar "X") (Cons (TVar "X") (Var "x") (Nil (TVar "X")))))
feval7 = TestCase (assertEqual "testnestedLambdas" (TLambda (TVar "Y") (Lambda "x" Nat (Cons Nat (Var "x") (Nil Nat)))) (evalStar (TApp nestedLambdas Nat)))

-- Tests for general recursion
fac = Lambda "f" (Fun Nat Nat) (Lambda "x" Nat (TIf (IsZero (Var "x")) (Succ Zero) (Mul (Var "x") (App (Var "f") (Pred (Var "x"))))))
facfix = Fix fac
--ivt (evalStar (App facfix (vt 5)))
feval1 = TestCase (assertEqual "evalSystemFID" (vt 3) (evalStar (App (TApp fid Nat) (vt 3))))
feval2 = TestCase (assertEqual "evalDoubleNatSucc" (vt 7) (evalStar (doubleNatSucc (vt 3))))
feval3 = TestCase (assertEqual "evalFactorialFix" (vt 120) (evalStar (App facfix (vt 5)))) --test fix eval

-- Typechecks
ftyp1 = TestCase (assertEqual "idForAll" (ForAll (TVar "X") (Fun (TVar "X") (TVar "X"))) (typeCheckSimple fid)) -- Simple typecheck forall
ftyp2 = TestCase (assertEqual "idForNat" (Fun Nat Nat) (typeCheckSimple (TApp fid Nat)))
ftyp3 = TestCase (assertEqual "doubleFromBook" (ForAll (TVar "X") (Fun (Fun (TVar "X") (TVar "X")) (Fun (TVar "X") (TVar "X")))) (typeCheckSimple double))
ftyp4 = TestCase (assertEqual "doubleNatArrowNat" (Fun (Fun (Fun Nat Nat) (Fun Nat Nat)) (Fun (Fun Nat Nat) (Fun Nat Nat))) (typeCheckSimple doubleNatArrowNat))
-- Referencing a type not in environment should fail
ftyp8 = TestCase (assertError "(TypeError:Unreferenced type variable → Nat)" (typeCheckSimple (Lambda "x" (TVar "X") (Zero))))
-- When the type variable is in the environment, it should no longer fail
ftyp9 = TestCase (assertEqual "checkBoundTypes" (ForAll (TVar "X") (Fun (TVar "X") Nat)) (typeCheckSimple (TLambda (TVar "X") (Lambda "x" (TVar "X") (Zero)))))

--Test general recursion:
ftyp5 = TestCase (assertEqual "factorialType" (Fun Nat Nat) (typeCheckSimple facfix))
ftyp6 = TestCase (assertEqual "checkQuadrupleTypes" (ForAll (TVar "Y") (Fun (Fun (TVar "Y") (TVar "Y")) (Fun (TVar "Y") (TVar "Y")))) (typeCheckSimple quadruple))

-- Typechecks for List
ftyp7 = TestCase (assertEqual "NatListType" (List Nat) (typeCheckSimple (TApp genericEmptyList Nat)))
ftyp10 = TestCase (assertEqual "NestedLambdaTypes" (ForAll (TVar "Y") (Fun Nat (List Nat))) (typeCheckSimple (TApp nestedLambdas Nat)))


-- List tests
genericEmptyList = TLambda (TVar "X") (Nil (TVar "X"))
listfail = TLambda (TVar "X") (Tail (TVar "X") (Nil (TVar ("X"))))

-- Function to create a list of nats up to maximum (argument)
nats = Fix (Lambda "g" (Fun Nat (List Nat)) (Lambda "w" Nat (TIf (IsZero (Var "w")) (Cons Nat Zero (Nil Nat)) (Cons Nat (Var "w") (App (Var "g") (Pred (Var "w")))))))

-- Polymorphic Map function
mymap = TLambda (TVar "X") (TLambda (TVar "Y")
          (Lambda "f" (Fun (TVar "X") (TVar "Y"))
            (Fix (Lambda "m" (Fun (List (TVar "X")) (List (TVar "Y")))
              (Lambda "l" (List (TVar "X"))
                (TIf (IsNil (TVar "X") (Var "l"))
                  (Nil (TVar "Y"))
                    (Cons (TVar "Y")
                     (App (Var "f") (Head (TVar "X") (Var "l")))
                     (App (Var "m") (Tail (TVar "X") (Var "l")))))
                      )))))

natmap = TApp (TApp mymap Nat) Nat
addOne = Lambda "r" Nat (Succ (Var "r"))  -- Simple Nat->Nat function that adds one to a nat
addOneMap = App natmap addOne -- Create a map function that adds one to each element in the list
testAddOneMap = App addOneMap (App nats (vt 2))

natboolmap = TApp (TApp mymap Nat) Bool
evenMap = App natboolmap (Lambda "r" Nat (Even (Var "r")))
testCheckBools = App evenMap (App nats (vt 5))
-- Checks for the application!
feval5 = TestCase (assertEqual "TestMap1" (Cons Nat (Succ (Succ (Succ Zero))) (Cons Nat (Succ (Succ Zero)) (Cons Nat (Succ Zero) (Nil Nat)))) (evalStar testAddOneMap))
feval6 = TestCase (assertEqual "TestMap2" (Cons Bool TFalse (Cons Bool TTrue (Cons Bool TFalse (Cons Bool TTrue (Cons Bool TFalse (Cons Bool TTrue (Nil Bool))))))) (evalStar testCheckBools))
ftyp11 = TestCase (assertEqual "MapType" (ForAll (TVar "X") (ForAll (TVar "Y") (Fun (Fun (TVar "X") (TVar "Y")) (Fun (List (TVar "X")) (List (TVar "Y")))))) (typeCheckSimple mymap))
ftyp12 = TestCase (assertEqual "MapTypeApls" (Fun (Fun Nat Nat) (Fun (List Nat) (List Nat))) (typeCheckSimple natmap))
ftyp13 = TestCase (assertEqual "FullyAppliedMap" (Fun (List Nat) (List Nat)) (typeCheckSimple addOneMap))

new_tests = [feval1, feval2, feval3, feval5, feval6, feval7, ftyp1, ftyp2, ftyp3, ftyp4, ftyp5, ftyp6, ftyp8, ftyp9, ftyp10, ftyp11, ftyp12, ftyp13]
run = runTestTT $ TestList (old_tests++new_tests)
