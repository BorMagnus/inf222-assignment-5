-- | State: keeping track of the state of an imperative computation.
-- This implementation allows values to span multiple locations.
-- The State consists of an environment (declared variables) and a store (computer memory).
-- • The environment is an association list of variable names and its starting location in memory.
-- • The store is an array of values indexed by locations. 
--   It is indifferent to how many locations a variable may span.
-- • The free location pointer keeps track of where the unused part of the memory starts.
--   The free locations start at the highest index in memory and grow downwards towards zero.
-- The State value API is aimed at explicit allocation of variables.
--
-- Locations have been hard coded to 16bit unsigned integers (256 values).
-- This allows up to 65536 memory cells, large enough to show interesting problems.
-- For debugging a memory range 0..255 is useful: this is small enough to allow full store dumps.
--
-- Author Magne Haveraaen
-- Since 2020-03-19, revised 2023-02-06

module PIPLstate where

-- Use Haskell's array data structure
import Data.Array
-- Use Haskell's 16bit word for locations
import Data.Word (Word16)


-------------------------
-- | Define the type for memory location indexing
type Location = Word16

-- | Maximum printable store size.
maxPrintable :: Location
maxPrintable = 300

-----------------------
-- | The state data structure: 
-- - an index for the next free memory location,
-- - an environment associaton list of variable name-store locations, and
-- - a store which for each location index keeps a value.
type State value = (Location,LEnvironment,Store value)

-- | A new State value is an empty environment and a default store.
-- - Location memsize: the number of locations the store will take (the memory size).
-- - value memelt: the default value of every memory cell.
newState :: Location -> value -> State value
newState memsize memelt = (memsize,[],emptyStore memsize memelt)

-- | Checks if a name is registered as a variable in the state
isVariable :: String -> State value -> Bool 
isVariable vname (freeloc,env,store) = lookup vname env /= Nothing

-- | Gets the value of the variable in the state: returns a list with the specified extent.
getValue :: String -> Location -> State value -> [value]
getValue vname extent (freeloc,env,store) = 
    getStoreValue (find vname env) extent store

-- | Changes the multilocation value associated with a known variable.
-- The new value should have the length corresponding to the variable's extent,
-- though there is no way to check this here.
changeValue :: Show value => String -> [value] -> State value -> State value
changeValue vname vals (freeloc,env,store) = (freeloc,env,setStoreValue (find vname env) vals store)

-- | Add a new variable and its multilocation value to the state.
addVariable :: Show value => String -> [value] -> State value -> State value
addVariable vname vals (freeloc,env,store) = (freeloc',env',store')
  where
    extent = fromIntegral (length vals)
    freeloc' = freeloc - extent
    env' = (vname,freeloc'):env
    store' = setStoreValue freeloc' vals store

-- | Creates a new variable name as an alias for an existing variable location.
createAlias :: String -> String -> State value -> State value
createAlias aliasvar vname (freeloc,env,store) = (freeloc,env',store)
  where
    env' = (aliasvar,find vname env):env


-- | Gets the value linked to the variable in an alternate environment:
-- find the variable's location in the alternate environment.
getValueAlternate :: String -> Location -> LEnvironment -> State value -> [value]
getValueAlternate vname extent altenv (freeloc,env,store) = 
    getStoreValue (find vname altenv) extent store


-- | Creates a new variable name in a new state as an alias
-- for an existing variable location taken from an alternate environment.
createAliasAlternate :: String -> String -> LEnvironment -> State value -> State value
createAliasAlternate aliasvar vname altenv (freeloc,env,store) = (freeloc,env',store)
  where
    env' = (aliasvar,find vname altenv):env

-- | Replaces the second state's store with the first state's store.
replaceStore :: State value -> State value -> State value
replaceStore (freeloc',env',store') (freeloc,env,store) = (freeloc,env,store')

-- | Gets the entire store component of the state.
getStore :: State value -> Store value
getStore (freeloc,env,store) = store

-- | Replaces the state's environment with the provided alternate environment.
replaceEnv :: LEnvironment -> State value -> State value
replaceEnv altenv (freeloc,env,store) = (freeloc,altenv,store)

-- | Get the environment component of the state.
getEnv :: State value -> LEnvironment
getEnv (freeloc,env,store) = env

-- | Replaces the state's free location and environment with the provided alternate free location and environment.
restoreStatus :: Location -> LEnvironment -> State value -> State value
restoreStatus altfreeloc altenv (freeloc,env,store) = (altfreeloc,altenv,store)

-- | Get the free location component of the state.
getFreeloc :: State value -> Location
getFreeloc (freeloc,env,store) = freeloc



-------------------------
-- | An environment instantiated for locations.
type LEnvironment = Environment Location

-- | The address (starting location) of a variable in memory
getAddress :: Name -> LEnvironment -> Location
getAddress vname env = find vname env


-------------------------
-- | An environment is used to keep track of name-attribute values.

-- | An environment is an association list mapping names to values.
-- Here the choice of value type is postponed.
type Environment value = [(Name,value)]
-- | A name is a string.
type Name = String

-- | Find a specific variable name in the environment: using lookup and Maybe monad.
find :: Name -> Environment value -> value
find vname env = case lookup vname env of
  Just v -> v
  Nothing -> error $ "Name not found: " ++ (show vname)

-- | Update the name associations in the second list with 
-- the corrresponding named value from the first list.
-- This corresponds to removing all local declarations from an inner scope (env1),
-- and updating the corresponding value association in the outer scope (env2).
updateEnv :: Environment value -> Environment value -> Environment value
updateEnv env1 ((vname,val):env2) = env'
  where
  env' = (case lookup vname env1 of
    Nothing -> (vname,val)
    Just val' -> (vname,val') ) : updateEnv env1 env2
updateEnv env1 [] = []


-----------------------
-- | A Store is an array of locations, where each location contains a value.
-- Store locations are used from the maximum downwards to the minimum array index.
type Store value = Array Location value

-- | Creates a store with index range defined by the maxBound location value
-- and uniform content given by the dval value.
emptyStore :: Location -> value -> Store value
emptyStore maxBound dval = (array (0,maxBound) [(i,dval) | i <- [0..maxBound]])

-- | Get the values stored at the given index with the given extent.
getStoreValue :: Location -> Location -> Store value -> [value]
getStoreValue addr 0 store = []
getStoreValue addr extent store = 
  if low <= addr && addr <= high - extent + 1
    then getData addr extent store
    else error $ "Not valid store indices from " ++ (show addr) ++ " to " ++ (show $ addr+extent) ++ 
      ", store bounds are " ++ (show low) ++ "<=" ++ (show high)
  where 
    (low,high) = bounds store
    getData addr 0 store = []
    getData addr length store = store ! addr : getData (addr+1) (length-1) store


-- | Set new values at the provided location.
setStoreValue :: Show value => Location -> [value] -> Store value -> Store value
setStoreValue addr vals store =
  if low <= addr && addr <= high - vsize + 1
  then store // updlist addr 0 vals
  else error $ "Not valid store indices from " ++ (show addr) ++ " to " ++ (show $ addr+vsize-1) ++
    ", store bounds are " ++ (show low) ++ "<=" ++ (show high)
    ++ if high <= maxPrintable
      then ", store=" ++ (show store)
      else ""
  where 
    (low,high) = bounds store
    vsize = fromIntegral (length vals)
    updlist addr i (val:vals) = (addr+i,val):updlist addr (i+1) vals
    updlist addr i [] = []


-----------------------
-- | Unit tests for State and values.
unittestState = do
  print $ "-- unittestState"
  -- putStrLn \$ "Empty state = " ++ (show newstate)
  let state1 = addVariable "v1" [1,2] (newState 25 1000) :: State Word16
  let state2 = addVariable "v2" [4] state1
  let state3 = addVariable "v3" [9] state2
  let (freeloc,env,store) = state3
  let state4 = changeValue "v2" [25] state3
  let state5 = addVariable "v4" [19] state4
  let state6 = addVariable "v5" [93,7,41] state5
  let state7 = createAlias "v6" "v1" state6
  let state8 = changeValue "v6" [42] state7
  let state3' = (freeloc,env,getStore state8)
  -- putStrLn $ "State8 = " ++ (show state8)
  -- putStrLn $ "State3' = " ++ (show state3')
  putStrLn $
    if [42,2] == getValue "v1" 2 state8
    && [25] == getValue "v2" 1 state8
    && [ 9] == getValue "v3" 1 state8
    && [19] == getValue "v4" 1 state8
    && [93,7,41] == getValue "v5" 3 state8
    && [42] == getValue "v6" 1 state8
    then "Unit tests hold"
    else "Tests failed"
  print $ state8
  print $ "end"

