{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use list literal" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Redundant $" #-}
-- | Examples for PIPL AST.
-- Extends the BIPL examples with procedures.
-- - Simple expression examples and declaration statements exloring scoping issues.
-- - Statement: Euclid's algorithm for computing quot and rem.
-- - Statmement: Computus (Easter Sunday algorithm).
-- - Procedure: exampleProcedures1 wraps Euclid's algorithm, Computus and an arbitrary sequence of assignments.
-- - Procedure: exampleProcedures2 some arbitrary procedures.
-- - Procedure: exampleProceduresSwap swap algorithms that reveal differences between reference and copy-in/copy-out semantics.
-- - Procedure: exampleProceduresFibonacci to demonstrate recursion.
-- 
-- Magne Haveraen 2023-02-08

module PIPLexamples where

import PIPLAST
-------------------------


-------------------------
-- | Tests for the interpreter/static analysis: exprList and declaxy
-- - Function vt maps from integers to the value domain
-- - Function eval evaluates expressions (interpreter)
-- - Function exec executes statements (interpreter)
-- - State newState is the starting configuration for the expressions.
-- The latter should include integer variables: "a" "x" "y"
test_evaluations_exec vt eval exec state newState = do
  -- Evaluate exprList with eval env for the integers.
  let resInt = map (eval state) exprList
  print $ "Evaluated test expressions with eval env: " ++ (show $ resInt)
  let state' = exec (exec (exec newState decly) declx) decla
  print $ "Executing declarations with exec " ++ if state == state' then "is OK" else "FAILED!"
  print "end"


-- | A list of expressions (test cases).
exprList :: [Expr]
exprList = [ expr0, expr1, expr2, expr3, expr4, expr5, expr6, expr7, expr_sqr_a, expr_f_x_y ]

-- Some constant expressions
-- 0
expr0 = Z
-- 3
expr1 = I $ I $ I $ Z
-- 7
expr2 = Plus (Mult (I $ I $ Z)(I $ I $ I $ Z)) (I Z)
-- 4
expr3 = Minus expr2 expr1
-- 33
expr4 = Mult expr1 (Plus expr2 expr3)
-- -26
expr5 = Plus (Mult expr0 expr1) (Minus expr2 expr4)
-- 1024
expr6 = Minus (I $ Mult expr4 expr4) (Plus expr4 expr4)
-- 0
expr7 = Ifte (Le expr1 expr3) expr5 expr6

-- | The square of variable "a"
expr_sqr_a = Mult (Var "a") (Var "a")
-- | The function f(x,y) = x*y + x + y
expr_f_x_y = Plus (Mult (Var "x") (Var "y")) (Plus (Var "x")(Var "y"))

-- | A syntactically problematic term: 
-- It is allowed in the metalanguage, but does not make sense.
exprn = Plus T (I $ I $ I $ I $ Le F (I $ I Z))

-- | Declaration statements for variables 
-- "a" = 7, "x",2, "y"=5)
decla = Decl "a" expr2
declx = Decl "x" (Minus expr3 (I $ I Z))
decly = Decl "y" (I $ expr3)
declaxy = Sequence [decly, declx, decla]

-- | Stements exposing interesting aspects of the semantics
-- 1: { { y=5; x=2; a=7; } ; res = f(x,y); }
stmtscope1 = Sequence [ declaxy, Decl "res" expr_f_x_y]
-- 2: { y=5; x=2; a=7 ; if <= 2 then res1 = a*a else res2 = f(x,y); }
stmtscope2 = Sequence ( [decly, declx, decla] ++ 
  [IfStmt (Le (Var "x")(I $ I Z)) (Assign "res1" expr_sqr_a)(Decl "res2" expr_f_x_y)])
-- 3: { y=5; x=2; a=7 ; while (1 <= x) { res = f(x,y); x = x-1}
stmtscope3 a = Sequence ( Decl "a" a:
  [While (Le (I Z) (Var "a"))
   (Sequence [Assign "res" expr_sqr_a, Assign "a" (Minus (Var "a")(I Z))])
  ])
stmtscope4 a = Sequence ( 
  Decl "b" expr_sqr_a:
  Decl "a" a:
  Sequence [declaxy,declaxy,
    Sequence [Sequence [Decl "b" expr_sqr_a, declaxy,Decl "c" expr_sqr_a]]]:
  While (Le (I Z) (Var "a"))
   (Sequence [Assign "res" expr_sqr_a, Assign "a" (Minus (Var "a")(I Z))]):
  [])
stmtscope5 = Sequence [declaxy, declaxy, decly, declx, decla] 

-- | Some examples that expose peculiarities of (runtime) scoping rules.
-- - Function exec executes statements (interpreter)
-- - isVariable is a function that checks if a variable is defined in the state.
-- - state with variable and values in a store.
test_scoping_exec exec isVariable state = do
  print $ "Some scoping issues"
  print $ "stmtscope1, res=" ++ (show $ isVariable "res" (exec state stmtscope1))
  print $ "stmtscope2, res1=" ++ (show $ isVariable "res1" (exec state stmtscope2))
  print $ "stmtscope2, res2=" ++ (show $ isVariable "res2" (exec state stmtscope2))
  print $ "stmtscope3 0, res=" ++ (show $ isVariable "res" (exec state (stmtscope3 Z)))
  print $ "stmtscope3 1, res=" ++ (show $ isVariable "res" (exec state (stmtscope3 (I Z))))
  print $ "stmtscope3 2, res=" ++ (show $ isVariable "res" (exec state (stmtscope3 (I $ I Z))))
  print $ "stmtscope4 2, res=" ++ (show $ isVariable "res" (exec state (stmtscope4 (I $ I Z))))
  print $ "done"


-----------------------
-- | Procedure for Euclidean division: (q,r) = x `quotRem` y
-- The quotient of x and y is assigned to q while the remainder of x and y is assigned to r.
{-
    procedure eucliddiv ( obs x,y:integer, out q,r:integer );
    begin
    q := 0;
    r := x;
    while y <= r do
        begin
        r := r - y;
        q := q + 1;
        end;
    end;
-}
eucliddiv_stmt :: Stmt
eucliddiv_stmt = Sequence [
  Assign "q" Z,
  Assign "r" (Var "x"),
  While (Le (Var "y") (Var "r"))
    (Sequence [
      Assign "r" (Minus (Var "r") (Var "y")),
      Assign "q" (Plus (Var "q") (I Z))
    ])
  ]

-- Test cases and oracles for the Euclid algorithm
type XY = (Integer,Integer)
type QR = (Integer,Integer)
type XYQR = (XY,QR)
eucliddiv_problems :: [XY]
eucliddiv_problems = [(13,7),(49,7),(16,32),(32,16),(32,15),(0,9),(1,9),(8,9),(9,9),(10,9)]
eucliddiv_answers :: [XYQR]
eucliddiv_answers = map (\(x,y) -> ((x,y),quotRem x y)) eucliddiv_problems

-- | Using the eucliddiv_problems test cases to check Euclid's algorithm.
-- - Function vt maps from integers to the value domain
-- - Function exec executes statements (interpreter)
-- - Association list env is a context environment for the algorithm.
test_euclid_exec :: (state -> Stmt -> state) -> (String -> state -> Integer) -> ([(String, Integer)] -> state) -> IO ()
test_euclid_exec exec find createState = do
  print $ "Testing Euclid's algorithm for quotient/reminder"
  let xyenvs = map (\((x,y),(q,r))->createState [("x",x),("y",y),("r",0),("q",0)]) eucliddiv_answers
  let qrvals = map (\((x,y),(q,r))->(q,r)) eucliddiv_answers
  let compute = map (\env->exec env eucliddiv_stmt) xyenvs
  let qrcomputed = map (\env->(find "q" env,find "r" env)) compute
  print $ if qrvals == qrcomputed then "OK" else "FAILED"
  print $ "end"

--------------------------
-- | Computus
{-
    (** Computing Easter Day for year Y using "Anonymous Gregorian algorithm". *)
    procedure computus ( obs Y:integer; out month,day:integer ) ;
    var a,b,c,d,e,f,g,h,i,k,l,m,n,o:integer;
    begin
    a := Y mod 19;
    b := Y div 100;
    c := Y mod 100;
    d := b div 4;
    e := b mod 4;
    f := (b + 8) div 25;
    g := (b - f + 1) div 3;
    h := (19*a + b - d - g + 15) mod 30;
    i := c div 4;
    k := c mod 4;
    l := (32 + 2*e + 2*i - h - k) mod 7;
    m := (a + 11*h + 22*l) div 451;
    n := (h + l - 7*m + 114) div 31;
    o := (h + l - 7*m + 114) mod 31;
    month := n;
    day := o + 1;
    end ;
-}
computus_2 = I (I Z)
computus_3 = I (I (I Z))
computus_4 = I (I (I (I Z)))
computus_7 = Plus computus_3 computus_4
computus_8 = I computus_7
computus_11 = Plus computus_4 computus_7
computus_15 = Plus computus_7 computus_8
computus_19 = I (I (I (Mult computus_4 computus_4)))
computus_22 = Mult computus_2 computus_11
computus_25 = I (I (I (I (I (I computus_19)))))
computus_30 = I (I (I (I (I computus_25))))
computus_31 = I (computus_30)
computus_32 = Plus computus_7 computus_25
computus_100 = Mult computus_4 computus_25
computus_114 = Minus (Plus computus_15 computus_100) (I Z)
computus_451 = Minus (Mult computus_4 computus_114) (I computus_4)
-- | Computing computus: the Easter day algorithm.
-- Input: "YEAR"; outputs: "month", "day"
computus_stmt :: Stmt
computus_stmt = Sequence [
    -- a := Y mod 19;
    Decl "x" (Var "YEAR"),
    Decl "y" computus_19,
    Decl "q" computus_451,
    Decl "r" computus_451,
    eucliddiv_stmt,
    Decl "a" (Var "r"),
    -- b := Y div 100;
    -- c := Y mod 100;
    Assign "x" (Var "YEAR"),
    Assign "y" computus_100,
    eucliddiv_stmt,
    Decl "b" (Var "q"),
    Decl "c" (Var "r"),
    -- d := b div 4;
    -- e := b mod 4;
    Assign "x" (Var "b"),
    Assign "y" computus_4,
    eucliddiv_stmt,
    Decl "d" (Var "q"),
    Decl "e" (Var "r"),
    -- f := (b + 8) div 25;
    Assign "x" ((Plus (Var "b")computus_8)),
    Assign "y" computus_25,
    eucliddiv_stmt,
    Decl "f" (Var "q"),
    -- g := (b - f + 1) div 3;
    Assign "x" (I (Minus (Var "b") (Var "f"))),
    Assign "y" computus_3,
    eucliddiv_stmt,
    Decl "g" (Var "q"),
    -- h := (19*a + b - d - g + 15) mod 30;
    Assign "x" computus_hexp,
    Assign "y" computus_30,
    eucliddiv_stmt,
    Decl "h" (Var "r"),
    -- i := c div 4;
    -- k := c mod 4;
    Assign "x" (Var "c"),
    Assign "y" computus_4,
    eucliddiv_stmt,
    Decl "i" (Var "q"),
    Decl "k" (Var "r"),
    -- l := (32 + 2*e + 2*i - h - k) mod 7;
    Assign "x" computus_lexp,
    Assign "y" computus_7,
    eucliddiv_stmt,
    Decl "l" (Var "r"),
    -- m := (a + 11*h + 22*l) div 451;
    Assign "x" (Plus (Plus (Var "a")(Mult computus_11(Var "h")))(Mult computus_22(Var "l"))),
    Assign "y" computus_451,
    eucliddiv_stmt,
    Decl "m" (Var "q"),
    -- n := (h + l - 7*m + 114) div 31;
    -- o := (h + l - 7*m + 114) mod 31;
    Assign "x" (Plus (Minus (Plus (Var "h")(Var "l")) (Mult computus_7(Var "m")))computus_114),
    Assign "y" computus_31,
    eucliddiv_stmt,
    Decl "n" (Var "q"),
    Decl "o" (Var "r"),
    -- month := n;
    -- day := o + 1;
    Assign "month" (Var "n"),
    Assign "day" (I (Var "o"))
    ]
-- h := (19*a + b - d - g + 15) mod 30;
computus_hexp :: Expr
computus_hexp = (Plus(Minus (Minus (Plus (Mult computus_19(Var "a"))(Var "b"))(Var "d")) (Var "g"))computus_15)
-- l := (32 + 2*e + 2*i - h - k) mod 7;
computus_lexp :: Expr
computus_lexp = (Minus(Minus (Plus (Plus computus_32(Mult computus_2(Var "e")))(Mult computus_2(Var "i"))) (Var "h")) (Var "k"))

type Date = (Integer, (Integer, Integer)) -- (Year,(Month,Day))
computus_answers :: [Date]
computus_answers = [(2023,(4,9)),(2022,(4,17)),(2021,(4,4)),(2020,(4,12)),(2019,(4,21)),(2011,(4,24)),(2008,(3,23)),(2038,(4,25))]

-- | Using the computus_answers test cases to check the Computus algorithm.
-- - Function vt maps from integers to the value domain
-- - Function exec executes statements (interpreter)
-- - Function find 
-- - Association list env is a context environment for the algorithm.
test_computus_exec :: (state -> Stmt -> state) -> (String -> state -> Integer) -> ([(String, Integer)] -> state) -> IO ()
test_computus_exec exec find createState = do
  print $ "Testing the Computus algorithm for finding Easter Sunday"
  let years = map (\ans->createState [("YEAR",fst ans),("month",0),("day",0)]) computus_answers
  let dates = map (\(y,(m,d))->(y,m,d)) computus_answers
  let compute = map (\state->exec state computus_stmt) years
  let computed = map (\state->(find "YEAR" state,find "month" state,find "day" state)) compute
  -- print $ dates
  -- print $ computed
  print $ if dates == computed then "OK" else "FAILED"
  print $ "end"


-- | Using the computus_answers test cases to check the Computus_copy algorithm.
-- - Function vt maps from integers to the value domain
-- - Function exec executes statements (interpreter)
-- - Function find 
-- - Association list env is a context environment for the algorithm.
test_computus_exec_copy :: (state -> Stmt -> state) -> (String -> state -> Integer) -> ([(String, Integer)] -> state) -> IO ()
test_computus_exec_copy exec find createState = do
  print $ "Testing the Computus copy algorithm for finding Easter Sunday"
  let years = map (\ans->createState [("YEAR",fst ans),("month",0),("day",0)]) computus_answers
  let dates = map (\(y,(m,d))->(y,m,d)) computus_answers
  let compute = map (\state->exec state computus_stmt_call_euclid) years
  let computed = map (\state->(find "YEAR" state,find "month" state,find "day" state)) compute
  -- print $ dates
  -- print $ computed
  print $ if dates == computed then "OK" else "FAILED"
  print $ "end"

--------------------------
-- | Procedure declarations

-- | Declarations of Euclid, Computus and something arbitrary.
exampleProcedures1 :: ProcDefinitions
exampleProcedures1 = ProcDef
  [proc_euclid
  ,proc_computus
  ,proc_computus2
  ,proc_simple
  ] 

-- | Wrapping up the Euclid algorithm as a procedure.
proc_euclid :: Procedure
proc_euclid = Proc "Euclid" [("x",(Obs,"Integer")),("y",(Obs,"Integer")),("q",(Out,"Integer")),("r",(Out,"Integer"))] eucliddiv_stmt
-- | Wrapping up the Computus algorithm as a procedure.
proc_computus = Proc "Computus" [("YEAR",(Upd,"Integer")),("month",(Out,"Integer")),("day",(Out,"Integer"))] computus_stmt
proc_computus2 = Proc "Computus_copy" [("YEAR",(Upd,"Integer")),("month",(Out,"Integer")),("day",(Out,"Integer"))] computus_stmt_call_euclid
-- | Some arbitrary algorithm as a procedure.
proc_simple :: Procedure
proc_simple = Proc "Simple" [("out",(Out,"Integer")),("y",(Out,"Integer")),("a",(Out,"Integer"))]
    (Sequence [
      Assign "a" expr4, 
      Assign "a" expr_sqr_a, 
      Assign "y" expr_sqr_a,
      Call "Euclid" [Left "a",Right expr2,Left "y",Left "a"],
      Assign "out" expr2
    ])


-- | Declarations of p2, p2, m, designed to show effects of parameter passing semantics.
exampleProcedures2 :: ProcDefinitions
exampleProcedures2 = ProcDef
  [ proc_p1
  , proc_p2
  , proc_m
  ]
proc_p1 = Proc "p1" [("x",(Obs,"Integer")),("y",(Out,"Integer"))]
  (Assign "y" (Plus (Var "x") (Var "x")))
proc_p2 = Proc "p2" [("x",(Upd,"Integer")),("y",(Upd,"Integer"))]
  (Sequence [
    Assign "y" (Plus (Var "x") (Var "y")),
    Assign "x" (Plus (Var "y") (Var "x"))
  ])
proc_m = Proc "m" [("a",(Upd,"Integer")),("b",(Out,"Integer")),("c",(Upd,"Integer"))]
  (Sequence [
    Decl "z" (Var "a"),
    Call "p1" [Right (Var "a"),Left "b"],
    Call "p1" [Left "a",Left "b"],
    Call "p2" [Left "a",Left "c"]
  ])


-- | Declarations for studying swap algorithms and effects of parameter passing semantics.
exampleProceduresSwap :: ProcDefinitions
exampleProceduresSwap = ProcDef
  [ proc_swap
  , proc_groupswap
  , proc_m_groupswap2
  , proc_m_groupswap1
  , proc_m_swap2
  , proc_m_swap1
  ]
-- | Swapping using intermediate storage
proc_swap = Proc "swap" [("x",(Upd,"Integer")),("y",(Upd,"Integer"))]
  (Sequence [
    Decl "t" (Var "y"),
    Assign "y" (Var "x"),
    Assign "x" (Var "t")
  ])
-- | Swapping using group operations (+ -).
proc_groupswap = Proc "groupswap" [("x",(Upd,"Integer")),("y",(Upd,"Integer"))]
  (Sequence [
    Assign "y" (Plus (Var "x") (Var "y")),
    Assign "x" (Minus (Var "y") (Var "x")),
    Assign "y" (Minus (Var "y") (Var "x"))
  ])
-- | Swapping two variables using groupswap
proc_m_groupswap2 = Proc "m_groupswap2" [("a",(Upd,"Integer")),("b",(Upd,"Integer"))]
  (Sequence [
    Call "groupswap" [Left "a",Left "b"]
  ])
-- | Swapping one variable with itself using groupswap
proc_m_groupswap1 = Proc "m_groupswap1" [("a",(Upd,"Integer"))]
  (Sequence [
    Call "groupswap" [Left "a",Left "a"]
  ])
-- | Swapping two variables using regular swap
proc_m_swap2 = Proc "m_swap2" [("a",(Upd,"Integer")),("b",(Upd,"Integer"))]
  (Sequence [
    Call "swap" [Left "a",Left "b"]
  ])
-- | Swapping one variable with itself using regular swap
proc_m_swap1 = Proc "m_swap1" [("a",(Upd,"Integer"))]
  (Sequence [
    Call "swap" [Left "a",Left "a"]
  ])


-- | Checking recursion using the Fibonacci function.
exampleProceduresFibonacci :: ProcDefinitions
exampleProceduresFibonacci = ProcDef
  [ proc_fibonacci ]
proc_fibonacci = Proc "fibonacci" [("n",(Obs,"Integer")),("fib",(Out,"Integer"))]
  (Sequence [
    IfStmt (Le (Var "n") (I Z))
     (Assign "fib" (I Z))
     (Sequence [
        Decl "fib1" Z,
        Decl "fib2" Z,
        Call "fibonacci" [Right (Minus (Var "n")(I Z)),Left "fib1"],
        Call "fibonacci" [Right (Minus (Var "n")(I $ I Z)),Left "fib2"],
        Assign "fib" (Plus(Var "fib1")(Var "fib2"))
     ])
  ])

-----------------------------------------------------------------------------------
-- | Copy of computing computus: the Easter day algorithm.
-- Input: "YEAR"; outputs: "month", "day"
computus_stmt_call_euclid :: Stmt
computus_stmt_call_euclid = Sequence [
    -- a := Y mod 19;
    Decl "x" (Var "YEAR"),
    Decl "y" computus_19,
    Decl "q" computus_451,
    Decl "r" computus_451,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "a" (Var "r"),
    -- b := Y div 100;
    -- c := Y mod 100;
    Assign "x" (Var "YEAR"),
    Assign "y" computus_100,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "b" (Var "q"),
    Decl "c" (Var "r"),
    -- d := b div 4;
    -- e := b mod 4;
    Assign "x" (Var "b"),
    Assign "y" computus_4,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "d" (Var "q"),
    Decl "e" (Var "r"),
    -- f := (b + 8) div 25;
    Assign "x" ((Plus (Var "b")computus_8)),
    Assign "y" computus_25,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "f" (Var "q"),
    -- g := (b - f + 1) div 3;
    Assign "x" (I (Minus (Var "b") (Var "f"))),
    Assign "y" computus_3,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "g" (Var "q"),
    -- h := (19*a + b - d - g + 15) mod 30;
    Assign "x" computus_hexp,
    Assign "y" computus_30,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "h" (Var "r"),
    -- i := c div 4;
    -- k := c mod 4;
    Assign "x" (Var "c"),
    Assign "y" computus_4,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "i" (Var "q"),
    Decl "k" (Var "r"),
    -- l := (32 + 2*e + 2*i - h - k) mod 7;
    Assign "x" computus_lexp,
    Assign "y" computus_7,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "l" (Var "r"),
    -- m := (a + 11*h + 22*l) div 451;
    Assign "x" (Plus (Plus (Var "a")(Mult computus_11(Var "h")))(Mult computus_22(Var "l"))),
    Assign "y" computus_451,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "m" (Var "q"),
    -- n := (h + l - 7*m + 114) div 31;
    -- o := (h + l - 7*m + 114) mod 31;
    Assign "x" (Plus (Minus (Plus (Var "h")(Var "l")) (Mult computus_7(Var "m")))computus_114),
    Assign "y" computus_31,
    Call "Euclid" [Left "x", Left "y", Left "q", Left "r"],
    Decl "n" (Var "q"),
    Decl "o" (Var "r"),
    -- month := n;
    -- day := o + 1;
    Assign "month" (Var "n"),
    Assign "day" (I (Var "o"))
    ]
-----------------------------------------------------------------------------------