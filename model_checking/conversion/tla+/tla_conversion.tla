--------------------------- MODULE tla_conversion ---------------------------

EXTENDS Integers, TLC

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
            (* Performing shift: k = n >> c *)
            \* FIXME: TLA+ shift operator ?
            l4: k := n >> c;
            
            (* Evaluating: k & 1 *)
            \* FIXME: TLA+ & operator ?
            l5: if (k % 2 == 1)
            {
                l6: print "1";
            }
            l7: else
            {
                l8: print "0";
            }
            
            (* Bumping the counter *)
            l5: c := c - 1;
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
      /\ k' = (n \div (10 ^ c)) % 10
      /\ pc' = "l10"
      /\ UNCHANGED << n, c >>

l10 == /\ pc = "l10"
       /\ PrintT(k)
       /\ pc' = "l5"
       /\ UNCHANGED << n, c, k >>

l5 == /\ pc = "l5"
      /\ c' = c - 1
      /\ pc' = "l3"
      /\ UNCHANGED << n, k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l10 \/ l5
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
\* Last modified Thu Feb 20 07:08:04 CET 2020 by Default
\* Last modified Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
\* Created Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
