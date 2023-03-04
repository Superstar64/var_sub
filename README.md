# Var Sub
This is my attempt typecheck the single effect calculus from "Monadic and Substructural Type Systems for Region-Based Memory Management"
with an algorithm inspired by simple-sub from "The Simple Essence of Algebraic Subtyping".
This was formerly integrated into [aith](https://github.com/Superstar64/aith), but it has since been replace with booloean unification.

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

## Update
This seem very closely related with ACI (associative-communative-idempotent) unification or just certain types of E-unification in general.
ACI unification works with semilattices, while Var Sub works with partially ordered sets.
Var Sub implements constant unification and it appears to be unitary for elementary unification, but not for constants unification.
See [(Unification Theory)](https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf) for definitions.
