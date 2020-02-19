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
      /\ pc' = "Done"
      /\ UNCHANGED << c, k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0
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
\* Last modified Wed Feb 19 18:11:39 CET 2020 by Default
\* Last modified Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
\* Created Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
