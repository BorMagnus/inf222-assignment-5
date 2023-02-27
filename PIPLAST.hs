-- | AST for a Procedural Imperative Programming Language (PIPL).
-- This extends L0502 BIPL2ASTassign with procedure declarations.
--
-- Magne Haveraen 2023-02-01 revised 2023-02-06

module PIPLAST where

-------------------------
-- | BTL for counting, calculations, choice and variables.
data Expr
  = Z
  | I Expr
  | Plus Expr Expr
  | Mult Expr Expr
  | Minus Expr Expr
  | T
  | F
  | And Expr Expr
  | Or Expr Expr
  | Not Expr
  | Le Expr Expr
  | Ifte Expr Expr Expr
  | Var VarName
  deriving (Show,Eq,Read)

-- | BIPL statements extended with procedure calls
-- Procedures are called by name, so need to be looked up in a database of procedure declarations.
data Stmt
  = Decl VarName Expr -- declaration and initialisation of a variable
  | Assign VarName Expr -- assignment to an already deaclared variable
  | While Expr Stmt
  | IfStmt Expr Stmt Stmt
  | Sequence [ Stmt ]
  | Call ProcName [Arg] -- Procdure call
  deriving (Show, Eq, Read)

-------------------------
-- | PIPL: procedures

-- | Procedure definition: name, parameterlist and body.
data Procedure =
  Proc ProcName [Param] Stmt
  deriving (Show, Eq, Read)

-- | Data base of procedure name-definitions (an association list of procedures).
data ProcDefinitions =
  ProcDef [Procedure]
  deriving (Show, Eq, Read)


-------------------------
-- | Parameter list: parameter name, information passing mode, type name.
type Param = (VarName,(Mode, TypeName))

-- | Parameter passing modes:
-- Obs: data can only be observed, arguments normally passed by value (copy-in)
-- Upd: data can be updated, arguments normally passed by reference
-- Out: data are only output, arguments normally passed by reference
data Mode = Obs | Upd | Out
  deriving (Show, Eq, Read)

-- | An argument can either be a variable name or an expression.
-- Left vname: can be used as an argument for any mode
-- Right expr: can only be used as an argument for Obs with value semantics.
type Arg = Either VarName Expr

-------------------------
-- | Names are strings.

-- | Variable names
type VarName = String
-- | Procedure names
type ProcName = String
-- | Type names
type TypeName = String

-------------------------