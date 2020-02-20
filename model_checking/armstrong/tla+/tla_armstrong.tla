--------------------------- MODULE tla_armstrong ---------------------------

EXTENDS Integers, Naturals, TLC

CONSTANTS TDATA, TSIZE

----------------------------------------------------------------------------

\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    variables 
        n,
        sum = 0,
        temp,
        remainder,
        digits = 0;
    {
        l0: skip;
    }
}
*)
----------------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, sum, temp, remainder, digits, pc

vars == << n, sum, temp, remainder, digits, pc >>

Init == (* Global variables *)
        /\ n = defaultInitValue
        /\ sum = 0
        /\ temp = defaultInitValue
        /\ remainder = defaultInitValue
        /\ digits = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ TRUE
      /\ pc' = "Done"
      /\ UNCHANGED << n, sum, temp, remainder, digits >>

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
    /\ var_in_bound(n)
    /\ var_in_bound(sum)
    /\ var_in_bound(temp)
    /\ var_in_bound(remainder)
    /\ var_in_bound(digits)

(* Partial correctness *)
post_condition ==
    /\ TRUE

safety_partial_correctness ==
    /\ pc = "Done" 
        => post_condition

(* Invariant *)
\* Local invariant for each pc
Il0 ==
    pc = "l0" =>
        /\ TRUE

\* Global invariant
i ==
    /\ pc \in {"l0", "Done"}
    /\ Il0

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Thu Feb 20 18:09:22 CET 2020 by Default
\* Last modified Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
\* Created Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
