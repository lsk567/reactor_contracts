#Contracts Verification of The Reaction Body

## Usage
The following command can check if the function(reaction body) satisfy the contract.
If not, it will also produce a counterexample
```
cbmc <file_name> --function <function_name> --trace
```

## From Reaction body to C Function
* Set the function arguments as the value of the trigger
* Set the affected ports and states as global variable
* Place the reaction body code
* Replace the SET() function as variable assignment
* Put the environment of the contract in ```__CPROVER_assume()``` and place it at the beginning of the function
* Put the guaranteee of the contract in ```__CPROVER_assert()``` and place it at the end of the function