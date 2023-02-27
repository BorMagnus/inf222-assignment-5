-- | Static semantics (compile time checking of code) for BIPL2AST:
-- - Check AST for static variable scoping disallowing redeclaration in subscopes (Java style)
-- - Check AST for static variable scoping allowing redeclaration in subscopes (C style)
-- - Type check AST assuring evaluation/assignment compatibility, but
--   allowing redeclaration of variables in subscopes (inner scopes).
--
-- Magne Haveraen 2023-02-01

module PIPLanalysis where

import PIPLAST
import PIPLexamples
import PIPLstate

import Data.Maybe (fromJust)


-------------------------
-- | Check expressions for unused variables.
-- - Right v: the (sub)expression uses only declared variables.
-- - Left msg: collated error messages from all subexpressions (including this expression).
-- Parameter v is the default value signalling a correct expression.
checkExpr :: Eq dt => dt -> DeclarationErrorEnvironment dt -> Expr -> ErrorStatus dt
checkExpr v env Z = Right v
checkExpr v env (I e) = checkExpr v env e
checkExpr v env (Plus e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env (Mult e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env (Minus e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env T = Right v
checkExpr v env F = Right v
checkExpr v env (And e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env (Or e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env (Not e) = checkExpr v env e
checkExpr v env (Le e1 e2) = bothDeclared (checkExpr v env e1) (checkExpr v env e2)
checkExpr v env (Ifte e0 e1 e2) =
  allDeclared v [checkExpr v env e0, checkExpr v env e1, checkExpr v env e2]
checkExpr v env (Var vname) =
  if lookup vname env == Nothing
    then Left $ "Undeclared(Expr) " ++ (show vname)
    else Right v

-------------------------
-- | Java style static scoping: no redeclaration in subscope allowed.
checkStmtJ :: DeclarationErrorEnvironment () -> Stmt -> DeclarationErrorEnvironment ()
checkStmtJ env stmt'@(Decl vname e1) = env'
  where
  val' = checkExpr () env e1
  env' = case lookup vname env of
    Nothing -> (vname,Right ()):addError () env [val']
    Just val ->
      (vname, Left "Redeclared"):addError () env [val', Left $ "Redeclared(Decl) " ++ (show vname)]
checkStmtJ env stmt'@(Assign vname e1) = env'
  where
  val' = checkExpr () env e1
  env' = case lookup vname env of
    Nothing -> (vname,Left "Undeclared"):addError () env [val',  Left $ "Undeclared(Assign) " ++ (show vname)]
    Just val ->
      (vname, val):addError () env [val']
checkStmtJ env stmt'@(While e stmt) = env'
  where
  val' = checkExpr () env e
  env1 = checkStmtJ (errorFree ():env) stmt
  env' = addError () env [val',extractErrors env1]
checkStmtJ env stmt'@(IfStmt e stmt1 stmt2) = env'
  where
  val' = checkExpr () env e
  env1 = checkStmtJ (errorFree ():env) stmt1
  env2 = checkStmtJ (errorFree ():env) stmt2
  env' = addError () env [val', extractErrors env1, extractErrors env2]
checkStmtJ env (Sequence stmts) = env'
  where
  envs = checkStmtJSeq (errorFree ():env) stmts
  env' = addError () env [extractErrors envs]

checkStmtJSeq :: DeclarationErrorEnvironment () -> [Stmt] -> DeclarationErrorEnvironment ()
checkStmtJSeq env (stmt:stmts) = env'
  where
    env1 = checkStmtJ env stmt
    env' = checkStmtJSeq env1 stmts
checkStmtJSeq env [] = env

-------------------------
-- | C style static scoping: redeclaration in subscope is allowed.
-- Maybe introduce a counter v to keep track of nesting depth.
-- Assumes all variables declared in an outer bock have lower block numbers.
-- checkStmtC :: DeclarationErrorEnvironment -> Stmt -> DeclarationErrorEnvironment
checkStmtC :: DeclarationErrorEnvironment Block -> Stmt -> DeclarationErrorEnvironment Block
checkStmtC env stmt'@(Decl vname e1) = env'
  where
  val' = checkExpr SB env e1
  env' = case lookup vname env of
    Nothing -> (vname,Right SB):addError SB env [val']
    Just (Left m) ->
      (vname, Left m):addError SB env [val', Left $ "Error-declared(Decl) " ++ (show vname)]
    Just (Right NB) ->
      (vname, Right SB):addError SB env [val']
    Just (Right SB) ->
      (vname, Left "Redeclared"):addError SB env [val', Left $ "Redeclared(Decl) " ++ (show vname)]
checkStmtC env stmt'@(Assign vname e1) = env'
  where
  val' = checkExpr SB env e1
  env' = case lookup vname env of
    Nothing -> (vname,Left "Undeclared"):addError SB env [val',  Left $ "Undeclared(Assign) " ++ (show vname)]
    Just val ->
      (vname, val):addError SB env [val']
checkStmtC env stmt'@(While e stmt) = env'
  where
  val' = checkExpr SB env e
  env1 = checkStmtC (errorFree SB:newBlock env) stmt
  env' = addError SB env [val', extractErrors env1]
checkStmtC env stmt'@(IfStmt e stmt1 stmt2) = updateEnv env' env
  where
  val' = checkExpr SB env e
  env1 = checkStmtC (errorFree SB:newBlock env) stmt1
  env2 = checkStmtC (errorFree SB:newBlock env) stmt2
  env' = addError SB env [val', extractErrors env1, extractErrors env2]
checkStmtC env (Sequence stmts) = env'
  where
  envs = checkStmtCSeq (errorFree SB:newBlock env) stmts
  env' = addError NB env [extractErrors envs]

checkStmtCSeq :: DeclarationErrorEnvironment Block -> [Stmt] -> DeclarationErrorEnvironment Block
checkStmtCSeq env (stmt:stmts) = env'
  where
    envs = checkStmtC env stmt
    env' = checkStmtCSeq envs stmts
checkStmtCSeq env [] = env



newBlock :: DeclarationErrorEnvironment Block -> DeclarationErrorEnvironment Block
newBlock env = map newBlockDecl env

newBlockDecl :: (Name, ErrorStatus Block) -> (Name, ErrorStatus Block)
newBlockDecl (vname,Right _) = (vname,Right NB)
newBlockDecl es = es


-------------------------
data Block = NB | SB
  deriving (Show, Eq, Read)

-- newBlock (Right _) = Right NB
-- newBlock (Left mg) = Left mg

-------------------------
data Type
  = TInteger
  | TBool
  -- TUser String 
  | TProc ([Type], Type)
  

type Type' = String
tinteger :: Type'
tinteger = "Integer"
tbool :: Type'
tbool = "Bool"

type TypeEnvironment = DeclarationErrorEnvironment Type'
type TypeError = ErrorStatus Type'


-- | Compute the type status of an expression: its type if possible, otherwise an appropriate error message.
typeExpr :: TypeEnvironment -> Expr -> TypeError
typeExpr tenv Z = Right tinteger
typeExpr tenv (I e) =
  allSameDeclaration "I" tinteger [typeExpr tenv e]
typeExpr tenv (Plus e1 e2) =
  allSameDeclaration "Plus" tinteger [typeExpr tenv e1, typeExpr tenv e2]
typeExpr tenv (Mult e1 e2) =
  allSameDeclaration "Mult" tinteger [typeExpr tenv e1, typeExpr tenv e2]
typeExpr tenv (Minus e1 e2) =
  allSameDeclaration "Minus" tinteger [typeExpr tenv e1, typeExpr tenv e2]
typeExpr tenv T = Right tbool
typeExpr tenv F = Right tbool
typeExpr tenv (And e1 e2) =
  allSameDeclaration "And" tbool [typeExpr tenv e1, typeExpr tenv e2]
typeExpr tenv (Or e1 e2) =
  allSameDeclaration "Or" tbool [typeExpr tenv e1, typeExpr tenv e2]
typeExpr tenv (Not e1) =
  allSameDeclaration "Not" tbool [typeExpr tenv e1]
typeExpr tenv (Le e1 e2) =
  bothDeclared
    (Right tbool)
    (allSameDeclaration "Le" tinteger [typeExpr tenv e1, typeExpr tenv e2])
typeExpr tenv (Ifte e0 e1 e2) =
  bothDeclared
    (allSameDeclaration "Ifte branches" tinteger [typeExpr tenv e1, typeExpr tenv e2])
    (allSameDeclaration "Ifte condition" tbool [typeExpr tenv e0])
typeExpr tenv (Var vname) =
  case lookup vname tenv of
    Nothing -> Left $ "Untyped variable " ++ (show vname)
    Just (Left msg) -> Left msg
    Just (Right tval) -> Right tval


-- | Compute the type environment for each statement type, taking extra care of propagating typing errors.
-- Type declarations are not exported by blocks: 
-- For every block the calling environment is restored, but enhanced with any typing problems from the subenvironment.
-- Type declarations are allowed to redeclare the type of a variable.
-- Assignments are not allowed to change the type of a variable, only its value.
typeStmt :: TypeEnvironment -> Stmt -> TypeEnvironment
typeStmt tenv (Decl vname e1) = tenv'
  where
  te1 = typeExpr tenv e1
  tdecl = (vname,te1)
  tenv1 = tdecl:tenv
  tenv' = addError "OK" tenv1 [te1]
typeStmt tenv (Assign vname e1) = tenv'
  where
  tvar = typeExpr tenv (Var vname)
  te1 = typeExpr tenv e1
  tassign = sameDeclaration "Assign" tvar te1
  tenv' = addError "OK" tenv [tassign]
typeStmt tenv stmt'@(While e0 stmt) = tenv'
  where
  te0' = allSameDeclaration "While condition" tbool [typeExpr tenv e0]
  tenv1 = typeStmt (errorFree "OK":tenv) stmt
  tenv' = addError "OK" tenv [te0', extractErrors tenv1]
typeStmt tenv stmt'@(IfStmt e0 stmt1 stmt2) = tenv'
  where
  te0' = typeExpr tenv e0
  tenv1 = typeStmt (errorFree "OK":tenv) stmt1
  tenv2 = typeStmt (errorFree "OK":tenv) stmt2
  tenv' = addError "OK" tenv [te0', extractErrors tenv1, extractErrors tenv2]
typeStmt tenv stmt'@(Sequence (stmts)) = tenv'
  where
  tenvs = typeStmtSeq (errorFree "OK":tenv) stmts
  tenv' = addError "OK" tenv [extractErrors tenvs]


-- | Compute the type environment after a sequence of statements
typeStmtSeq :: TypeEnvironment -> [Stmt] -> TypeEnvironment
typeStmtSeq tenv (stmt:stmts) = tenvs
  where
  tenv1 = typeStmt tenv stmt
  tenvs = typeStmtSeq tenv1 stmts
typeStmtSeq env [] = env

-------------------------
-- | Compute the type environment for a procedure definition
typeProc :: TypeEnvironment -> Procedure -> TypeEnvironment
typeProc env (Proc pname params stmt) = tenv'
  where
  ptypes = map (\(_,(_,t)) -> t) params
  tenv1 = foldl (\env' (name,(_,t)) -> (name, Right t):env') env params
  tenv2 = typeStmt (errorFree "OK":tenv1) stmt
  tenv' = addError "OK" tenv1 []

-- | Compute the type status of a procedure call: its return type if possible, otherwise an appropriate error message.
typeProcCall :: TypeEnvironment -> ProcName -> [TypeName] -> Either String Type
typeProcCall tenv pname args =
  case lookup pname tenv of
    Nothing -> Left $ "Undefined procedure " ++ show pname
    Just (Left msg) -> Left msg
    Just (Right (TProc ptypes t)) ->
      if length args /= length ptypes
      then Left $ "Invalid number of arguments for procedure " ++ show pname
      else allSameDeclaration ("Procedure " ++ show pname ++ " call") t [typeExpr tenv e | (t, e) <- zip ptypes args]
    Just (Right t) -> Left $ "Procedure " ++ show pname ++ " is not defined"


-------------------------
test_analysis_checkJ = do
  test_analysis_check () checkStmtJ

test_analysis_checkC = do
  test_analysis_check NB checkStmtC

test_analysis_checkType = do
  test_analysis_check "Integer" typeStmt
  let v = tinteger
  let env1 = ("x",Right v):("y",Right v):("q",Right v):("r",Right v):newDeclarationErrorEnvironment v
  if   Right "Bool" == typeExpr (("v", Right "Integer"):newDeclarationErrorEnvironment "OK") (Le (I (I (Var "v"))) Z)
    && Right "Bool" == typeExpr  env1  (Le (Var "y") (Var "r"))
    && Left "Untyped variable \"c\"" == typeExpr (("a",Right tinteger):("b",Right tinteger):newDeclarationErrorEnvironment "OK") (Le (Var "c") (Le (Var "a") (Var "b")))
    && Left "Untyped variable \"c\"\nLe mismatch m1=\"Integer\" m2=\"Bool\"" == typeExpr (("a",Right tinteger):("b",Right tbool):newDeclarationErrorEnvironment "OK") (Le (Var "c") (Le (Var "a") (Var "b")))
    && Left "Le mismatch m1=\"Integer\" m2=\"Bool\"" == typeExpr (("c",Right tinteger):("a",Right tinteger):("b",Right tinteger):newDeclarationErrorEnvironment "OK") (Le (Var "c") (Le (Var "a") (Var "b")))
    then print $ "Type expression analysis OK"
    else print $ "Type expression analysis FAIL"
  if True
    -- Declaration statement
    && [("",Right "OK"),("a",Right "Integer"),("a",Right "MyType"),("",Right "OK")] == typeStmt (("a",Right "MyType"):newDeclarationErrorEnvironment "OK") (Decl "a" (I Z))
    -- Assignment statements
    && [("",Right "OK"),("a",Right "MyType"),("",Right "OK")] == typeStmt (("a",Right "MyType"):newDeclarationErrorEnvironment "OK") (Assign "a" (Var "a"))
    && [("",Left "Assign mismatch m1=\"MyType\" m2=\"Integer\""),("a",Right "MyType"),("",Right "OK")] == typeStmt (("a",Right "MyType"):newDeclarationErrorEnvironment "OK") (Assign "a" (I Z))
    && Left "some error" == extractErrors (typeStmt (("a",Right "MyType"):("",Left "some error"):newDeclarationErrorEnvironment "OK") (Assign "a" (Var "a")) )
    && Left "some error\nNot mismatch m1=\"Bool\" m2=\"Integer\"" == extractErrors (typeStmt (("a",Right "MyType"):("",Left "some error"):newDeclarationErrorEnvironment "OK") (Assign "a" (Not Z)) )
    && Left "some error\nAssign mismatch m1=\"MyType\" m2=\"Bool\"" == extractErrors (typeStmt (("a",Right "MyType"):("",Left "some error"):newDeclarationErrorEnvironment "OK") (Assign "a" (Not T)) )
    -- Sequence statemets
    && Left "And mismatch m1=\"Bool\" m2=\"Integer\"" == extractErrors (typeStmt (("a",Right "MyType"): newDeclarationErrorEnvironment "OK") (Sequence [Assign "a" (Var "a"), Decl "a" (And T Z)]) )
    && Left "hey\nUntyped variable \"res\"\nI mismatch m1=\"Integer\" m2=\"Bool\"" == extractErrors (typeStmt (("",Left "hey"):("rest",Right "Mine"):("a",Right tinteger):env1) (Sequence [Assign "res" expr_sqr_a, Assign "a" (Minus (Var "a") (I T))]) )
    then print $ "Type statement analysis OK"
    else print $ "Type statement analysis FAIL"
  print $ "end type analysis"


-------------------------
-- | Instantiating an environment to keep track of static semantic errors.

-- | Declaration error environment: an environment with the name-error status bindings.
-- 
type DeclarationErrorEnvironment dt = Environment (ErrorStatus dt)

-- | The error status value. The Either monad has two components:
-- - Left which will contain a string of error messages.
-- - Right which contains no information (the unit type denoted by a pair of paranthesis).
type ErrorStatus dt = Either String dt

-- | A newly declared environment must contain ("",Right())
-- This special variable name is used to propagate the errors.
newDeclarationErrorEnvironment :: dt -> DeclarationErrorEnvironment dt
newDeclarationErrorEnvironment v = errorFree v:[]

errorFree :: dt -> (Name, ErrorStatus dt)
errorFree v = ("",Right v)

addError :: dt -> DeclarationErrorEnvironment dt -> [ErrorStatus dt] -> DeclarationErrorEnvironment dt
addError v env list = ("",allDeclared v (extractErrors env:list)):env

-- | Extract the accumulated error status in the environment.
-- This is achieved by looking up the omnipresent error name "".
extractErrors :: DeclarationErrorEnvironment dt -> ErrorStatus dt
extractErrors env = fromJust $ lookup "" env

-- | Print the accumulated error messages nicely formatted.
printErrors :: DeclarationErrorEnvironment dt -> IO ()
printErrors env | Left str <- extractErrors env = putStrLn str
printErrors env | Right _ <- extractErrors env = putStr ""
printErrors env = error $ "Sentinel missing"

-- | Propagate correctness of declarations, or combine any error message, i.e., returns:
-- - Right _: only when both arguments are Right, chooses the first correctness message.
-- - Left _: concatenation of all error messages from below.
-- This is like a disjunction of errors, or a conjunction of correctness.
-- It is associative, with (Right _) as neutral element and (Left _) as absorbing.
bothDeclared :: ErrorStatus dt -> ErrorStatus dt -> ErrorStatus dt
bothDeclared (Left m1) (Left m2) = Left (m1++"\n"++m2)
bothDeclared (Left m1) (Right m2) = Left (m1)
bothDeclared (Right m1) (Left m2) = Left (m2)
bothDeclared (Right m1) (Right m2) = Right m1

-- | Reduce a list of possible error messages into one compound message. Returns:
-- - Right v: when all argument status are (Right _)
-- - Left _: concatenation of all error messages.
-- This is a fold on the associative function bothDeclared with (Right _) as unit element.
allDeclared :: dt -> [ErrorStatus dt] -> ErrorStatus dt
allDeclared v list = foldl bothDeclared (Right v) list


-- | Propagate correctness of declarations, or combine any error message, i.e., returns:
-- - Right _: only when both arguments are Right and equal. Generates an error message otherwise.
-- - Left _: concatenation of all error messages from below.
-- This is like a disjunction of errors, or a conjunction of correctness.
-- It is associative, with matching (Right _) as neutral element and (Left _) as absorbing.
-- The message msg is prepended to the mismatch error message.
sameDeclaration :: (Eq dt, Show dt) => String -> ErrorStatus dt -> ErrorStatus dt -> ErrorStatus dt
sameDeclaration msg (Left m1) (Left m2) = Left (m1++"\n"++m2)
sameDeclaration msg (Left m1) (Right m2) = Left (m1)
sameDeclaration msg (Right m1) (Left m2) = Left (m2)
sameDeclaration msg (Right m1) (Right m2) =
  if m1 == m2 then Right m1 else Left $ msg ++ " mismatch m1=" ++ (show m1) ++ " m2=" ++ (show m2)

-- | Reduce a list of possible error messages into one compound message. Returns:
-- - Right v: when all argument status are (Right v). Generates an error message otherwise.
-- - Left _: concatenation of all error messages from below.
-- This is a left fold on the associative function sameDeclaration with (Right v) as starting element.
allSameDeclaration :: (Eq dt, Show dt) => String -> dt -> [ErrorStatus dt] -> ErrorStatus dt
allSameDeclaration msg v list = foldl (sameDeclaration msg)  (Right v) list


-------------------------

-------------------------
-- | Check statements by static analysis.
-- Test environments mimicking some relevance.
test_analysis_check v check = do
  print $ "Testing static analysis"
  let env1 = ("x",Right v):("y",Right v):("q",Right v):("r",Right v):newDeclarationErrorEnvironment v
  putStrLn $ "eucliddiv_stmt "
  printErrors $ check env1 eucliddiv_stmt
  let env2 = ("x",Right v):("y",Right v):("q",Right v):("r",Right v):newDeclarationErrorEnvironment v
  putStrLn $ "stmtscope1 "
  printErrors $ check env2 stmtscope1
  putStrLn $ "stmtscope2 "
  printErrors $ check env2 stmtscope2
  putStrLn $ "stmtscope3 "
  printErrors $ check env2 (stmtscope3 (I $ I Z))
  putStrLn $ "stmtscope4 "
  printErrors $ check env2 (stmtscope4 (I $ I Z))
  putStrLn $ "stmtscope5 "
  printErrors $ check (newDeclarationErrorEnvironment v) stmtscope5
  let env3 = ("YEAR",Right v):("month",Right v):("day",Right v):newDeclarationErrorEnvironment v
  putStrLn $ "computus_stmt "
  printErrors $ check env3 computus_stmt
  print $ "end"

