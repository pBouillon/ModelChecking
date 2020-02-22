--------------------------- MODULE tla_conversion ---------------------------

EXTENDS Integers, Naturals, Reals, TLC

CONSTANT TO_CONVERT

----------------------------------------------------------------------------

\* Utilities functions
right_shift == [to_shift, shifts \in Int |-> 0]

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
            l4: k := n \div (2 ^ c);
            
            (* Evaluating: k & 1 *)
            l5: if (k % 2 = 0) print "1" else print "0";
            
            (* Bumping the counter *)
            l6: c := c - 1;
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
      /\ k' = (n \div (2 ^ c))
      /\ pc' = "l5"
      /\ UNCHANGED << n, c >>

l5 == /\ pc = "l5"
      /\ IF k % 2 = 0
            THEN /\ PrintT("1")
            ELSE /\ PrintT("0")
      /\ pc' = "l6"
      /\ UNCHANGED << n, c, k >>

l6 == /\ pc = "l6"
      /\ c' = c - 1
      /\ pc' = "l3"
      /\ UNCHANGED << n, k >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6
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
    /\ var_in_bound(k)

(* Partial correctness *)
post_condition ==
    \* No post condition to assert, this program
    \* Does not compute any result
    TRUE
            
safety_partial_correctness ==
    /\ pc = "Done" 
        => post_condition

(* Invariant *)
\* Local invariant for each pc
Il0 ==
    pc = "l0" =>
        /\ n = defaultInitValue
        /\ c = defaultInitValue
        /\ k = defaultInitValue
    
Il1 ==
    pc = "l1" =>
        /\ n = TO_CONVERT
    
Il2 ==
    pc = "l2" =>
        \* `print` statement, nothing to evaluate
        /\ TRUE
    
Il3 ==
    pc = "l3" =>
        /\ c <= 31
        /\ c >= -1
    
Il4 ==
    pc = "l4" =>
        /\ c >= 0
    
Il5 ==
    pc = "l5" =>
        \* `k` should be the result of the right shift
        \* of `n` by `c`
        /\ k = n \div 2 ^ c
        \* `k` should give the binary equivalent of the current
        \* power of two
        /\ (k = 1 \/ k = 0)

Il6 ==
    pc = "l6" =>
        \* `print` statement, nothing to evaluate
        /\ TRUE

\* Global invariant
i ==
    /\ pc \in {
        "l0", "l1", "l2", "l3", "l4", 
        "l5", "l6", "Done"}
    /\ Il0 /\ Il1 /\ Il2 /\ Il3 /\ Il4
    /\ Il5 /\ Il6

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Sat Feb 22 10:49:33 CET 2020 by Default
\* Created Wed Feb 19 18:01:15 CET 2020 by Pierre Bouillon
