--------------------------- MODULE tla_insertion ---------------------------
EXTENDS Naturals, TLC

----------------------------------------------------------------------------
\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    variables 
        n,
        array \in 1..1000,
        c,
        d,
        t;
            
    {
        skip;
    }
}
*)

----------------------------------------------------------------------------
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, array, c, d, t, pc

vars == << n, array, c, d, t, pc >>

Init == (* Global variables *)
        /\ n = defaultInitValue
        /\ array \in 1..1000
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ t = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << n, array, c, d, t >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

----------------------------------------------------------------------------
\* Assertions

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 22:31:26 CET 2020 by Pierre Bouillon
\* Created Mon Jan 13 13:32:31 CET 2020 by Pierre Bouillon
