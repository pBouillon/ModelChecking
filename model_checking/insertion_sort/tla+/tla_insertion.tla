--------------------------- MODULE tla_insertion ---------------------------

----------------------------------------------------------------------------
\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    {
        skip;
    }
}
*)

----------------------------------------------------------------------------
\* BEGIN TRANSLATION
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

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
\* Last modified Mon Jan 13 13:42:46 CET 2020 by Pierre Bouillon
\* Created Mon Jan 13 13:32:31 CET 2020 by Pierre Bouillon
