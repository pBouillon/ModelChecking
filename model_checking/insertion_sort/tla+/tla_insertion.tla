--------------------------- MODULE tla_insertion ---------------------------
EXTENDS Integers, Naturals, TLC

CONSTANTS TSIZE, TDATA
\* TODO: ASSERT TSIZE == TDATA.size

----------------------------------------------------------------------------
\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    variables 
        n,
        array = 1..1000,
        c,
        d,
        t;       
    {
        (* Number of numbers to sort *)
        n := TSIZE;
    
        (* Array filling *)
        c := 0;
        
        while (c < n) 
        {
            (* Arrays start at 1 in TLA+, so adding 1 to the indexes *)
            array[c + 1] := TDATA[c + 1];
            c := c + 1;
        };
        
        (* Perform sorting algorithm *)
        c := 1;
        while (c <= n - 1)
        {
            d := c;
            
            while (d > 0
                (* Arrays start at 1 in TLA+, so adding 1 to the indexes *)
                /\ array[d + 1] < array[d - 1 + 1])
            {
                (* Arrays start at 1 in TLA+, so adding 1 to the indexes *)
                t := array[d + 1];
                array[d + 1] := array[d - 1];
                array[d - 1] := t;
            };
            
            c := c + 1;
        };
        
        (* Program's ending *)
        print "Sorted list in ascending order: \n"
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
        /\ array = 1..1000
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ t = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ n' = TSIZE
         /\ c' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << array, d, t >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF c < n
               THEN /\ array' = [array EXCEPT ![c + 1] = TDATA[c + 1]]
                    /\ c' = c + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ c' = 1
                    /\ pc' = "Lbl_3"
                    /\ array' = array
         /\ UNCHANGED << n, d, t >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF c <= n - 1
               THEN /\ d' = c
                    /\ pc' = "Lbl_4"
               ELSE /\ PrintT("Sorted list in ascending order: \n")
                    /\ pc' = "Done"
                    /\ d' = d
         /\ UNCHANGED << n, array, c, t >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ IF    d > 0
               
               /\ array[d + 1] < array[d - 1 + 1]
               THEN /\ t' = array[d + 1]
                    /\ array' = [array EXCEPT ![d + 1] = array[d - 1]]
                    /\ pc' = "Lbl_5"
                    /\ c' = c
               ELSE /\ c' = c + 1
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << array, t >>
         /\ UNCHANGED << n, d >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ array' = [array EXCEPT ![d - 1] = t]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << n, c, d, t >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

----------------------------------------------------------------------------
\* Assertions

=============================================================================
\* Modification History
\* Last modified Tue Jan 14 12:33:15 CET 2020 by Pierre Bouillon
\* Created Mon Jan 13 13:32:31 CET 2020 by Pierre Bouillon
