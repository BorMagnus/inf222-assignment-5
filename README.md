# Assignment 5 - INF222

## 1.

Algoritghm *computus_stmt_call_euclid* is located at line 440, where computus_stmt is switched with a call to the to *proc_euclid* procedure called "Euclid", where the first two arguments ("x" and "y") are input parameters and the last two arguments ("q" and "r") are output parameters. This is tested with the use of *test_computus_copy* (line 286) in *PIPLinterpreter.hs* that uses a copy of test_computus_exec called *test_computus_exec_copy* (line 309) in *PIPLexamples.hs*:
```
ghci> test_computus_copy
"Testing the Computus copy algorithm for finding Easter Sunday"
"OK"
"end"
```

Also added procedure "*Coputus_copy*" to *exampleProcedures1* for testing.

## 2. a)

In the modified *buildArgs* function (line 184 to 188), I created copies of the argument values for *Upd* and *Out* parameters by calling *getValueAlternate* to retrieve the value of the argument variable and then add that value as a new variable with the parameter's name to the local environment.
## 2. b)
### Output from PIPLinterpreter.hs with testcallsemantics:
```
ghci> testcallsemantics
"Testing swap procedures"
"Copy-in/copy-out semantics"
Swap [34,42]: [VI 42,VI 34]
Swap [42,42]: [VI 42,VI 42]
GroupSwap [34,42]: [VI 42,VI 34]
GroupSwap [42,42]: [VI 42,VI 42]
"Reference semantics, swapping two variables"
Swap [34,42]: [VI 42,VI 34]
Swap [42,42]: [VI 42,VI 42]
GroupSwap [34,42]: [VI 42,VI 34]
GroupSwap [42,42]: [VI 42,VI 42]
"Reference semantics, swapping a variable with itself"
Swap [42]: [VI 42]
GroupSwap [42]: [VI 0]
```
### Output from PIPLcopyinterpreter.hs with testcallsemantics:
```
ghci> testcallsemantics
"Testing swap procedures"
"Copy-in/copy-out semantics"
Swap [34,42]: [VI 42,VI 34]
Swap [42,42]: [VI 42,VI 42]
GroupSwap [34,42]: [VI 42,VI 34]
GroupSwap [42,42]: [VI 42,VI 42]
"Reference semantics, swapping two variables"
Swap [34,42]: [VI 34,VI 42]
Swap [42,42]: [VI 42,VI 42]
GroupSwap [34,42]: [VI 34,VI 42]
GroupSwap [42,42]: [VI 42,VI 42]
"Reference semantics, swapping a variable with itself"
Swap [42]: [VI 42]
GroupSwap [42]: [VI 42]
```
In reference semantics, variables are passed by reference, meaning that when a procedure is called with a variable as an argument, any changes made to the variable inside the procedure affect the original variable in the calling environment. When running the reference semantics tests, you can see that the "Swap [34,42]" and "GroupSwap [34,42]" tests produce different results than the corresponding tests with [42,42] as the input. This is because the two variables are swapped in place, and in the case where they are different, this results in the values being swapped. However, when the input is [42,42], both variables have the same value, so swapping them in place does not change anything.

In contrast, copy-in/copy-out semantics pass variables by value, meaning that a copy of the variable is made and passed to the procedure, and any changes made to the copy inside the procedure do not affect the original variable in the calling environment. When running the copy-in/copy-out semantics tests, you can see that all tests produce the same results, regardless of the input values. This is because the procedure is not changing the original variables, but instead creating new copies of them and swapping the values of those copies.

  

## 3.
