# CLPGeneralization

## How to use
Consult main.pl then launch test_class(C,K,W,N) with 
- C = class identifier (classes are defined in db.pl)
- K = parameter K for Algorithm 1
- W = parameter W for Algorithm 2
- N = number of tests to perform

This will execute three algorithms (2 bruteforces + 1 k-swap abstraction) N times and compare their mean execution times as well as the accuracy of the k-swap algorithms based on the N test cases. 

## Files
- mcg.pl is an implementation of the bruteforce algorithm generating all possible generalizations and selecting an MCG
- exhaustive_renamings.pl is an implementation of the bruteforce algorithm generating all possible *renamings* and selecting an MCG
- generalization_abstration.pl contains the algorithms studied in the paper (k-swap)
- au_complexity contains predicates that compute the complexity of a given instance of the anti-unification problem, based on number of possible generalizations/variable combinations 
