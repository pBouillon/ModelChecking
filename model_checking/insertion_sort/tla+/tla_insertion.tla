--------------------------- MODULE tla_insertion ---------------------------
EXTENDS Integers, Naturals, TLC

CONSTANTS TDATA, TSIZE

----------------------------------------------------------------------------
\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    variables 
        n,
        array = [i \in 1..1000 |-> 0];
        c,
        d,
        t;       
    {
        (* Number of numbers to sort *)
        l0: n := TSIZE;
    
        (* Array filling *)
        l1: c := 0;
        l2: while (c < n) 
        {
            (* Arrays start at 1 in TLA+, so adding 1 to the indexes *)
            l3: array[c + 1] := TDATA[c + 1];
            l4: c := c + 1;
        };
        
        (* Perform sorting algorithm *)
        l5: c := 1;
        l6: while (c <= n - 1)
        {
            l7: d := c;
            
            (* Arrays start at 1 in TLA+, so adding 1 to the indexes *)
            l8: while (d > 0 /\ array[d + 1] < array[d - 1 + 1])
            {
                (* Arrays start at 1 in TLA+, so add 1 to the indexes *)
                l9: t := array[d + 1];
                l10: array[d + 1] := array[d - 1 + 1];
                l11: array[d - 1 + 1] := t;
                
                l12: d := d - 1;
            };
            
            l13: c := c + 1;
        };
        
        (* Program's ending *)
        l14: print "Sorted list in ascending order:";
        
        l15: c := 0;
        l16: while(c <= n - 1) 
        {
            l17: print array[c + 1];
            l18: c := c + 1;
        }
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
        /\ array = [i \in 1..1000 |-> 0]
        /\ c = defaultInitValue
        /\ d = defaultInitValue
        /\ t = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ n' = TSIZE
      /\ pc' = "l1"
      /\ UNCHANGED << array, c, d, t >>

l1 == /\ pc = "l1"
      /\ c' = 0
      /\ pc' = "l2"
      /\ UNCHANGED << n, array, d, t >>

l2 == /\ pc = "l2"
      /\ IF c < n
            THEN /\ pc' = "l3"
            ELSE /\ pc' = "l5"
      /\ UNCHANGED << n, array, c, d, t >>

l3 == /\ pc = "l3"
      /\ array' = [array EXCEPT ![c + 1] = TDATA[c + 1]]
      /\ pc' = "l4"
      /\ UNCHANGED << n, c, d, t >>

l4 == /\ pc = "l4"
      /\ c' = c + 1
      /\ pc' = "l2"
      /\ UNCHANGED << n, array, d, t >>

l5 == /\ pc = "l5"
      /\ c' = 1
      /\ pc' = "l6"
      /\ UNCHANGED << n, array, d, t >>

l6 == /\ pc = "l6"
      /\ IF c <= n - 1
            THEN /\ pc' = "l7"
            ELSE /\ pc' = "l14"
      /\ UNCHANGED << n, array, c, d, t >>

l7 == /\ pc = "l7"
      /\ d' = c
      /\ pc' = "l8"
      /\ UNCHANGED << n, array, c, t >>

l8 == /\ pc = "l8"
      /\ IF d > 0 /\ array[d + 1] < array[d - 1 + 1]
            THEN /\ pc' = "l9"
            ELSE /\ pc' = "l13"
      /\ UNCHANGED << n, array, c, d, t >>

l9 == /\ pc = "l9"
      /\ t' = array[d + 1]
      /\ pc' = "l10"
      /\ UNCHANGED << n, array, c, d >>

l10 == /\ pc = "l10"
       /\ array' = [array EXCEPT ![d + 1] = array[d - 1 + 1]]
       /\ pc' = "l11"
       /\ UNCHANGED << n, c, d, t >>

l11 == /\ pc = "l11"
       /\ array' = [array EXCEPT ![d - 1 + 1] = t]
       /\ pc' = "l12"
       /\ UNCHANGED << n, c, d, t >>

l12 == /\ pc = "l12"
       /\ d' = d - 1
       /\ pc' = "l8"
       /\ UNCHANGED << n, array, c, t >>

l13 == /\ pc = "l13"
       /\ c' = c + 1
       /\ pc' = "l6"
       /\ UNCHANGED << n, array, d, t >>

l14 == /\ pc = "l14"
       /\ PrintT("Sorted list in ascending order:")
       /\ pc' = "l15"
       /\ UNCHANGED << n, array, c, d, t >>

l15 == /\ pc = "l15"
       /\ c' = 0
       /\ pc' = "l16"
       /\ UNCHANGED << n, array, d, t >>

l16 == /\ pc = "l16"
       /\ IF c <= n - 1
             THEN /\ pc' = "l17"
             ELSE /\ pc' = "Done"
       /\ UNCHANGED << n, array, c, d, t >>

l17 == /\ pc = "l17"
       /\ PrintT(array[c + 1])
       /\ pc' = "l18"
       /\ UNCHANGED << n, array, c, d, t >>

l18 == /\ pc = "l18"
       /\ c' = c + 1
       /\ pc' = "l16"
       /\ UNCHANGED << n, array, d, t >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9 \/ l10
           \/ l11 \/ l12 \/ l13 \/ l14 \/ l15 \/ l16 \/ l17 \/ l18
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
    /\ var_in_bound(c)
    /\ var_in_bound(d)
    /\ var_in_bound(t)
    /\ \A val \in 0..TSIZE : var_in_bound(array[val + 1])

(* Partial correctness *)
safety_partial_correctness ==
    /\ pc = "Done" 
        => \A val \in 1..TSIZE : 
            IF val < TSIZE
                \* Compare the current value with the next one
                THEN array[val] <= array[val + 1]
                \* The last value is "ordered" with itself
                ELSE TRUE 

(* Global invariant *)
i ==
    /\ pc \in {
        "l0", "l1", "l2", "l3", "l4", 
        "l5", "l6", "l7", "l8", "l9", 
        "l10", "l11", "l12", "l13", "l14", 
        "l15", "l16", "l17", "l18", "Done"}
        \* WiP

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Tue Jan 28 20:50:51 CET 2020 by Pierre Bouillon
\* Created Mon Jan 13 13:32:31 CET 2020 by Pierre Bouillon
