# Var Sub
This is my attempt typecheck the single effect calculus from "Monadic and Substructural Type Systems for Region-Based Memory Management"
with an algorithm inspired by simple-sub from "The Simple Essence of Algebraic Subtyping".
This is planned to be eventually integrated into [aith](https://github.com/Superstar64/aith).

# Current status of the algorithm
Only rigid and flexible type variables are allowed inside subtyping constraints.
In simple sub a flexible variable will never be in the lower bounds position of another flexible variable.
This is due to `constrain (Variable x) (Variable x')` prefering the `constrain (Variable x) e` case.
This means that flexible variables can only contain rigid variables in their lower bounds.
This hopefully makes preventing recursive types (cycles) easier to reason about because rigid variables don't have free (flexible) variables.

# Future ideas / goals
* Transative reduction to simplify constraints
* Figure out if this algorithm can produce principle types
* Maybe try having a singular lower rigid bound on flexible variabless
* Reason about general saneness properties like order of equations not mattering.
