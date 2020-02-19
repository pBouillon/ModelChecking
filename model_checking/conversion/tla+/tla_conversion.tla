--------------------------- MODULE tla_conversion ---------------------------

EXTENDS Integers, Naturals, TLC

CONSTANT TO_CONVERT

----------------------------------------------------------------------------

\* PlusCal conversion of the algorithm

(*
--algorithm conversion {
    variables 
        n,
        c,
        k;       
    {
        (* Decimal number to convert *)
        l0: n := TO_CONVERT;
        
        l1: print << n, " in binary number system is:" >>;
        
        (* Begin conversion *)
        l2: c := 31;
        
        l3: while (c >= 0)
        {
            (* TODO: conversion logic *)
        
            l4: c := c - 1;
        }
    }
}
*)

----------------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, c, k, pc

vars == << n, c, k, pc >>

Init == (* Global variables *)
        /\ n = defaultInitValue
        /\ c = defaultInitValue
        /\ k = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ n' = TO_CONVERT
      /\ pc' = "l1"
      /\ UNCHANGED << c, k >>

l1 == /\ pc = "l1"
      /\ PrintT(<< n, " in binary number system is:" >>)
      /\ pc' = "l2"
      /\ UNCHANGED << n, c, k >>

l2 == /\ pc = "l2"
      /\ c' = 31
      /\ pc' = "l3"
      /\ UNCHANGED << n, k >>

l3 == /\ pc = "l3"
      /\ IF c >= 0
            THEN /\ pc' = "l4"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << n, c, k >>

l4 == /\ pc = "l4"
      /\ c' = c - 1
      /\ pc' = "l3"
      /\ UNCHANGED << n, k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

----------------------------------------------------------------------------

\* Assertions

(* Runtime errors *)
\* Check domain of var X
var_in_bound(X) ==
    /\ (X # defaultInitValue) => X \in Int

\* Check domain of all used vars
safety_runtime ==
    /\ TRUE

(* Partial correctness *)
post_condition ==
    TRUE
            
safety_partial_correctness ==
    /\ pc = "Done" 
        => post_condition

(* Invariant *)
\* Local invariant for each pc
Il0 ==
    /\ TRUE

\* Global invariant
i ==
    /\ TRUE

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Wed Feb 19 18:19:03 CET 2020 by Default
\* Last modified Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
\* Created Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
