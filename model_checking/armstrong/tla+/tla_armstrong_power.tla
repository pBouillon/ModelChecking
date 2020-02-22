--------------------------- MODULE tla_armstrong_power ---------------------------

EXTENDS Integers, Naturals, TLC

CONSTANTS N, R

----------------------------------------------------------------------------------

\* PlusCal conversion of the algorithm

(*
--algorithm conversion {
    variables 
        c,
        p,
        n = N,
        r = R;       
    {
        (* Initialize variable *)
        l0: p := 1;

        (* Initialize the counter *)
        l1: c := 1;

        l2: while (c <= r)
        {
            l3: p := p * n;

            (* Bump the counter *)
            l4: c:= c + 1;
        }
    }
}
*)

----------------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES c, p, n, r, pc

vars == << c, p, n, r, pc >>

Init == (* Global variables *)
        /\ c = defaultInitValue
        /\ p = defaultInitValue
        /\ n = N
        /\ r = R
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ p' = 1
      /\ pc' = "l1"
      /\ UNCHANGED << c, n, r >>

l1 == /\ pc = "l1"
      /\ c' = 1
      /\ pc' = "l2"
      /\ UNCHANGED << p, n, r >>

l2 == /\ pc = "l2"
      /\ IF c <= r
            THEN /\ pc' = "l3"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << c, p, n, r >>

l3 == /\ pc = "l3"
      /\ p' = p * n
      /\ pc' = "l4"
      /\ UNCHANGED << c, n, r >>

l4 == /\ pc = "l4"
      /\ c' = c + 1
      /\ pc' = "l2"
      /\ UNCHANGED << p, n, r >>

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
    /\ var_in_bound(c)
    /\ var_in_bound(p)
    /\ var_in_bound(n)
    /\ var_in_bound(r)

(* Partial correctness *)
post_condition ==
    /\ p = n ^ r
            
safety_partial_correctness ==
    /\ pc = "Done" 
        => post_condition

(* Invariant *)
\* Local invariant for each pc
Il0 ==
    pc = "l0" =>
        /\ c = defaultInitValue
        /\ p = defaultInitValue
        /\ n = N
        /\ r = R
    
Il1 ==
    pc = "l1" =>
        /\ p = 1
    
Il2 ==
    pc = "l2" =>
        /\ c >= 1
        /\ c <= r + 1
        
Il3 ==
    pc = "l3" =>
        /\ c <= r
            
Il4 ==
    pc = "l4" =>
        /\ p = n ^ c

\* Global invariant
i ==
    /\ pc \in {
        "l0", "l1", "l2", "l3", "l4", "Done"}
    /\ Il0 /\ Il1 /\ Il2 /\ Il3 /\ Il4

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Sat Feb 22 11:19:28 CET 2020 by Default
\* Created Sat Feb 22 11:05:24 CET 2020 by Pierre Bouillon
