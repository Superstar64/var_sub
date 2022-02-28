# Var Sub
This is my attempt typecheck the single effect calculus from "Monadic and Substructural Type Systems for Region-Based Memory Management"
with an algorithm inspired by simple-sub from "The Simple Essence of Algebraic Subtyping".
This is planned to be eventually integrated into [aith](https://github.com/Superstar64/aith).

# Current status of the algorithm
This algorithm is similiar to simple-sub expect that subtyping constrains are limited to only allow rigid and flexible type variables
and cycles with flexible variables `[a <= b, b <= a]` generate equality constraints `[a = b]`.

In simple sub a flexible variable will never be in the lower bounds position of another flexible variable.
This is due to `constrain (Variable x) (Variable x')` prefering the `constrain (Variable x) e` case.
This means that flexible variables can only contain rigid variables in their lower bounds.
This makes preventing cycles (recursive types) easier to reason about because rigid variables don't have free (flexible) variables.

Flexible variables also keep track of the greatest lower bound rather then keeping track of all the lower bounds.
The idea is that rigid variables in type schemes should only contain upper bounds and not lower bounds to simplify reasoning and syntax.
So when generalization occurs, some sort of type defaulting is going to have to occur to elimate flexible rigids that have rigid lower bounds
and picking the greatest lower bound is the most reasonable choice here.  

# Future ideas / goals
* Transative reduction to simplify constraints
* Figure out if this algorithm can produce principle types
* Reason about general saneness properties like order of equations not mattering.
