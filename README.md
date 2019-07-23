# CLPGeneralization

## How to use
Consult main.pl then launch test_class(C,K,W,N) with 
- C = class identifier
- K = parameter K for Algorithm 1
- W = parameter W for Algorithm 2
- N = number of tests to perform

## Files
- mcg.pl is an implementation of the bruteforce algorithm generating all possible generalizations and selecting an MCG
- exhaustive_renamings.pl is an implementation of the bruteforce algorithm generating all possible *renamings* and selecting an MCG
- generalization_abstration.pl contains the algorithms studied in the paper (k-swap)
- au_complexity contains predicates that compute the complexity of a given instance of the anti-unification problem, based on number of possible generalizations/variable combinations 
