-- | An interpreter for Procedural Imperative Programming Language (PIPL):
-- uses static scoping, supports recursive procedures, and
-- uses parameter passing by value for expressions (Obs) and by reference for Upd/Out.
-- Extended L0502 BIPL2static with procedures.
--
-- Uses semantics: ValueDomain'' = VI Integer | VB Bool
-- Each of these take 1 store location.
--
-- Magne Haveraen 2023-02-01 revised 2023-02-06

module PIPLinterpreter where

-- Use the PIPL AST
import PIPLAST

-- Use state (environment and store) for PIPL
import PIPLstate

-- Include some examples for testing
import PIPLexamples
-------------------------

-------------------------
-- | The semantic domain are the integers and booleans
data ValueDomain'' = VI Integer | VB Bool 
  deriving (Show,Eq,Read)

-- | Embedding (converting) an integer to a value domain element.
iembed :: Integer -> ValueDomain''
iembed i = VI i
-- | Extracting an integer from the value domain
iproject :: ValueDomain'' -> Integer
iproject (VI i) = i
iproject x = error $ "Not an integer: "++(show x)
-- | Embedding (converting) a boolean to a value domain element.
bembed :: Bool -> ValueDomain''
bembed b = VB b
-- | Extracting a boolean from the value domain
bproject :: ValueDomain'' -> Bool
bproject (VB b) = b
bproject x = error $ "Not a boolean: "++(show x)


-- | The state is for value domain ValueDomain''.
type State'' = State ValueDomain''
-- | Setting aside a printable amount of store memory for small test examples.
memorySize :: Location
memorySize = 255 :: Location

-- | Each data item takes 1 location.
dataSize :: Location
dataSize = 1

-------------------------
-- | The interpreter for static scoping.

-- | Evaluator from expressions to the integer and boolean value domain
eval :: State'' -> Expr -> [ValueDomain'']
eval state Z = [VI 0] 
eval state (I e) = [VI (1 + e')] 
  where [VI e'] = eval state e
eval state (Plus e1 e2) = [VI (e1' + e2')]
  where
    [VI e1'] = eval state e1
    [VI e2'] = eval state e2
eval state (Mult e1 e2) = [VI (e1' * e2')]
  where
    [VI e1'] = eval state e1
    [VI e2'] = eval state e2
eval state (Minus e1 e2) = [VI (e1' - e2')]
  where
    [VI e1'] = eval state e1
    [VI e2'] = eval state e2
eval state T = [VB True]
eval state F = [VB False]
eval state (And e1 e2) = [VB (e1' && e2')]
  where
    [VB e1'] = eval state e1
    [VB e2'] = eval state e2
eval state (Or e1 e2) = [VB (e1' || e2')]
  where
    [VB e1'] = eval state e1
    [VB e2'] = eval state e2
eval state (Not e1) = [VB (not e1')]
  where
    [VB e1'] = eval state e1
eval state (Le e1 e2) = [VB (e1' <= e2')]
  where
    [VI e1'] = eval state e1
    [VI e2'] = eval state e2
eval state (Ifte e0 e1 e2) = if e0' then (eval state e1) else (eval state e2)
  where
    [VB e0'] = eval state e0
eval state (Var vname) = getValue vname dataSize state
-- eval state _ = error "WRONG"


-------------------------

-- | Execute the statements and update the state:
-- using value (copy-in) semantics for Obs and reference semantics for Upd/Out parameters, 
-- see the semantic function perform for details.
-- Uses static scoping: variables are scoped by the block where they are declared.
-- A variable has to be declared/initialised before use, but can be (re)declared many times.
-- Procedure declaration are provided as a context to be able to select which procedure to call. 
exec :: ProcDefinitions -> State'' -> Stmt -> State''
exec procdef state (Decl vname e1) = addVariable vname (eval state e1) state
exec procdef state (Assign vname e1) =  
  if isVariable vname state 
    then changeValue vname (eval state e1) state 
    else error $ "Variable has not been declared, vname=" ++ (show vname)
exec procdef state (While e stmt) = replaceStore state' state 
  where
    [VB e'] = eval state e
    state' = if e' 
      then exec procdef (exec procdef state stmt) (While e stmt)
      else state
exec procdef state (IfStmt e stmt1 stmt2) = replaceStore state' state 
  where
    [VB e'] = eval state e
    state' = if e' 
      then exec procdef state stmt1
      else exec procdef state stmt2
exec procdef state (Sequence stmts) = replaceStore state' state
  where
    state' = execSeq procdef state stmts
exec procdef state (Call pname args) = replaceStore state' state
  where
  proc  = findProcedure procdef pname args
  state' = perform procdef proc args state

-- | Execute a list of statements updating the store on the way.
execSeq :: ProcDefinitions -> State'' -> [Stmt] -> State''
execSeq procdef state (stmt:stmts) = state''
  where
    state' = exec procdef state stmt
    state'' = execSeq procdef state' stmts
execSeq procdef state [] = state

-- | Find the intended procedure in the procedure list.
-- Here the search is based on the name only.
-- Overloading is possible by also matching the argument list with the procedure's parameters.
findProcedure :: ProcDefinitions -> ProcName -> [Arg] -> Procedure
findProcedure (ProcDef (proc@(Proc pname params stmt):procs)) procname args =
  if pname == procname
    then proc
    else findProcedure (ProcDef procs) procname args
findProcedure (ProcDef []) procname args =
  error $ "Procedure name not found: " ++ (show procname)

-------------------------

-- | Perform a procedure on the provided arguments.
-- - Obs parameters are by value (copy-in) to a local variable with the parameter's name.
-- - Out/Upd parameters are by reference: a local variable with the parameter's name is an alias for the argument variable.
-- See function buildArgs for details.
-- Build a local environment for the procedure by evaluating the arguments in the calling context.
perform :: ProcDefinitions -> Procedure -> [Arg] -> State'' ->  State''
perform procdef (Proc procname param stmt) args state = replaceStore state' state
  where
  outerenv = getEnv state
  innerstate = replaceEnv [] state
  callstate = (buildArgs outerenv param args innerstate)
  returnstate = exec procdef callstate stmt
  state' = replaceEnv outerenv returnstate

-- | Build a new state for executing a procedure body:
-- Evaluate the procedures arguments in an old environment, creating the new state.
-- This is done by pattern matching the parameter declaration with the proper actual argument.
-- - Obs parameters are by value (copy-in) to a local variable with the parameter's name.
-- - Out/Upd parameters are by reference: a local variable with the parameter's name is an alias for the argument variable.
buildArgs :: LEnvironment -> [Param] -> [Arg] -> State'' -> State''
buildArgs oldenv (param@(vpname,(Obs,tname)):params) (arg@(Left vaname):args) state = state'
  where
  val = getValueAlternate vaname dataSize oldenv state
  state' = buildArgs oldenv params args (addVariable vpname val state)
buildArgs oldenv (param@(vpname,(Obs,tname)):params) (arg@(Right e):args) state =  state'
  where
  oldstate = replaceEnv oldenv state
  val = eval oldstate e
  state' = buildArgs oldenv params args (addVariable vpname val state)
buildArgs oldenv (param@(vpname,(Upd,tname)):params) (arg@(Left vaname):args) state =  
  buildArgs oldenv params args (createAliasAlternate vpname vaname oldenv state)
buildArgs oldenv (param@(vpname,(Out,tname)):params) (arg@(Left vaname):args) state =  
  buildArgs oldenv params args (createAliasAlternate vpname vaname oldenv state)
buildArgs oldenv [] [] state = state
buildArgs oldenv params args state = error $ "Argument list mismatch: params="++(show params)++" args="++(show args)


-------------------------
-- | Run a named procedure from GHC's command line using copy-in/copy-out semantics for the outermost procedure call.
-- This code is parameterised by the interpreter and is thus not connected to any specific value domain.
-- ProcDefinitions procdef: (list of) procedure definitons.
-- ProcName procname: the unique name in procdef of the procedure to be called.
-- [value] args: list of inflowing arguments to the procedure (matches Obs/Upd parameters).
-- value dval: default value to fill the empty store.
-- (ProcDefinitions -> State value -> Stmt -> State value) exec: the interpreter to be used, implicitly deciding the value domain.
run :: Show value => ProcDefinitions -> ProcName -> [value] -> value -> (ProcDefinitions -> State value -> Stmt -> State value) -> [value]
run procdef procname args dval exec = outs
  where
  -- Create new state with all parameters in fresh variables
  varvals = zip (map show [1..length args]) args
  args' = []
  proc = findProcedure procdef procname args'
  state = newState memorySize dval
  outs = runProc procdef state proc args dval exec

-- | Run a specific procedure in a given state using copy-in/copy-out semantics.
-- This code is parameterised by the interpreter and is thus not connected to any specific value domain.
-- ProcDefinitions procdef: (list of) procedure definitons possibly called by the code.
-- (State value) state: the staring state for the procedure call.
-- Procedure proc: the procedure being called.
-- [value] args: list of inflowing arguments to the procedure (matches Obs/Upd parameters).
-- value dval: default value to fill the empty store.
-- (ProcDefinitions -> State value -> Stmt -> State value) exec: the interpreter to be used, implicitly deciding the value domain.
runProc :: Show value => ProcDefinitions -> State value -> Procedure -> [value] -> value -> (ProcDefinitions -> State value -> Stmt -> State value) -> [value]
runProc procdefs state proc@(Proc pname params stmt) args dval exec = outs
  where
  state1 = matchIns state params args [dval]
  state2 = exec procdefs state1 stmt
  outs = matchOuts state2 params

-- | Matching arguments with Obs/Upd parameters, using a default value for Out parameters,
-- to update a state with providing the context for executing a procedure's body.
-- (State value) state: the state to be updated for the parameters.
-- [Param] params: declared parameter list for the procedure.
-- [value] args: list of inflowing (Obs/Upd) argument values.
-- [value] dval: default arguments value to be used to initialise Out parameters.
-- Return: state prepared for calling a procedure's body.
matchIns :: Show value => State value -> [Param] -> [value] -> [value] -> State value
matchIns state (param@(vpname,(Obs,tname)):params) (arg:args) dval = 
  matchIns (addVariable vpname [arg] state) params args dval
matchIns state (param@(vpname,(Upd,tname)):params) (arg:args) dval = 
  matchIns (addVariable vpname [arg] state) params args dval
matchIns state (param@(vpname,(Out,tname)):params) args dval = 
  matchIns (addVariable vpname dval state) params args dval
matchIns state [] [] dval = state
matchIns state params args dval = error $ "MatchIns mismatch: params="++(show params)++" args="++(show args)

-- | Matching a procedure output parameters (Upd/Out) and extracting them from the state.
-- (State value) state: state after return from a procedure call.
-- [Param] params: the procedure's parameter list (with modes).
-- Return: a list of the procedures output values (Upd/Out).
matchOuts :: Show value => State value -> [Param] -> [value]
matchOuts state (param@(vpname,(Obs,tname)):params) = 
  matchOuts state params
matchOuts state (param@(vpname,(Upd,tname)):params) = 
  head (getValue vpname dataSize state):matchOuts state params
matchOuts state (param@(vpname,(Out,tname)):params) = 
  head (getValue vpname dataSize state):matchOuts state params
matchOuts state [] = [] 
-- error $ show state

-- | Accumulate a state by accumulating variable name-expression pairs into it.
accumulateState :: Show value => State value -> [(VarName, Expr)] -> (State value -> Expr -> [value]) -> State value
accumulateState state decls eval = head $ scanr (\(x,e)st->addVariable x (eval st e) st) state decls


-------------------------
-- | Tests for the interpreter.

-- | Evaluation of expressions and executing statements,
teststatements = do
  test_evaluations
  test_scoping
  test_scoping_alt
  test_euclid
  test_computus

-- expression
test_evaluations = test_evaluations_exec iembed eval (exec (ProcDef []))
  (createState [("a",7),("x",2),("y",5)]) 
  (newState 5 (bembed False))
-- statements in a minimal environment
test_scoping = test_scoping_exec (exec (ProcDef [])) isVariable 
  $ createState [("res1",-2),("res",9)]
-- statements in a larger environment
test_scoping_alt = test_scoping_exec (exec (ProcDef [])) isVariable
  $ createState [("a",42),("x",31),("y",20),("res",9),("res1",-2),("res2",-13)]
-- Executing Euclid's algorithm on a predetermined set of test data.
-- Note that the dot means function composition, thus (f.g.h x)==(f(g(h x)))
test_euclid :: IO ()
test_euclid = test_euclid_exec (exec (ProcDef [])) (\str->iproject.head.getValue str dataSize) createState
-- Executing the computus algorithm on a predetermined set of test data.
test_computus = test_computus_exec (exec (ProcDef [])) (\str->iproject.head.getValue str dataSize) createState
test_computus_copy = test_computus_exec_copy (exec (ProcDef [proc_euclid])) (\str->iproject.head.getValue str dataSize) createState

-- | Inititalise a state from an assoication list of variable names and integers.
createState varIntList = head $ scanr (\(x,v)->addVariable x [iembed v]) (newState 21 (bembed False)) varIntList

-------------------------
-- | Test some procedures.
testprocedures = do
  print $ "Testing procedures"
  putStr $ "Euclid: "
  print $ run exampleProcedures1 "Euclid" [VI 34,VI 12] (VI 42) exec
  putStr $ "Computus: "
  print $ run exampleProcedures1 "Computus" [VI 2023] (VI 24) exec
  putStr $ "Simple: "
  print $ run exampleProcedures1 "Simple" [] (VI 12) exec
  putStr $ "p1: "
  print $ run exampleProcedures2 "p1" [VI 34] (VI 12) exec
  putStr $ "p2: "
  print $ run exampleProcedures2 "p2" [VI 34,VI 12] (VI 12) exec
  putStr $ "m: "
  print $ run exampleProcedures2 "m" [VI 34,VI 12] (VI 12) exec

-- | Testing different call semantics, note especially the last case.
testcallsemantics = do
  print $ "Testing swap procedures"
  print $ "Copy-in/copy-out semantics"
  putStr $ "Swap [34,42]: "
  print $ run exampleProceduresSwap "swap" [VI 34,VI 42] (VI 12) exec
  putStr $ "Swap [42,42]: "
  print $ run exampleProceduresSwap "swap" [VI 42,VI 42] (VI 12) exec
  putStr $ "GroupSwap [34,42]: "
  print $ run exampleProceduresSwap "groupswap" [VI 34,VI 42] (VI 12) exec
  putStr $ "GroupSwap [42,42]: "
  print $ run exampleProceduresSwap "groupswap" [VI 42,VI 42] (VI 12) exec
  print $ "Reference semantics, swapping two variables"
  putStr $ "Swap [34,42]: "
  print $ run exampleProceduresSwap "m_swap2" [VI 34,VI 42] (VI 12) exec
  putStr $ "Swap [42,42]: "
  print $ run exampleProceduresSwap "m_swap2" [VI 42,VI 42] (VI 12) exec
  putStr $ "GroupSwap [34,42]: "
  print $ run exampleProceduresSwap "m_groupswap2" [VI 34,VI 42] (VI 12) exec
  putStr $ "GroupSwap [42,42]: "
  print $ run exampleProceduresSwap "m_groupswap2" [VI 42,VI 42] (VI 12) exec
  print $ "Reference semantics, swapping a variable with itself"
  putStr $ "Swap [42]: "
  print $ run exampleProceduresSwap "m_swap1" [VI 42] (VI 12) exec
  putStr $ "GroupSwap [42]: "
  print $ run exampleProceduresSwap "m_groupswap1" [VI 42] (VI 12) exec


-- | Testing recursion: the Fibonacci function.
testrecursion = do
  print $ "Testing a recursive Fibonacci procedure"
  putStr $ "Fibonnaci [5]: "
  print $ run exampleProceduresFibonacci "fibonacci" [VI 5] (VI 12) exec
  putStr $ "Fibonnaci [10]: "
  print $ run exampleProceduresFibonacci "fibonacci" [VI 10] (VI 12) exec
  putStr $ "Fibonnaci [15]: "
  print $ run exampleProceduresFibonacci "fibonacci" [VI 15] (VI 12) exec
  putStr $ "Fibonnaci [20]: "
  print $ run exampleProceduresFibonacci "fibonacci" [VI 20] (VI 12) exec
  putStr $ "Fibonnaci [25]: "
  print $ run exampleProceduresFibonacci "fibonacci" [VI 25] (VI 12) exec

