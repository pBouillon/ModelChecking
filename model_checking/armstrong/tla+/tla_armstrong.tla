--------------------------- MODULE tla_armstrong ---------------------------

EXTENDS Integers, Naturals, Reals, TLC

CONSTANTS N

----------------------------------------------------------------------------

\* PlusCal conversion of the algorithm

(*
--algorithm insertion_sort {
    variables 
        n = N,
        sum = 0,
        temp,
        remainder,
        digits = 0;
    {
        (* Initialize the counter *)
        l0: temp := n;
        
        (* Count the number of digits *)
        l1: while (temp # 0)
        {
            l2: digits := digits + 1;
            l3: temp := temp \div 10;
        };
        
        (* Initialize the counter *)
        l4: temp := n;
        
        l5: while (temp # 0)
        {
            l6: remainder := temp % 10;
            
            (* Since we proved the `power(a, b)` function, and given       *)
            (* that the precondition `remainder` and `digits` are integers *)
            (* we can use the post condition as this function: `a ^ b`     *)
            l7: sum := sum + remainder ^ digits;
            
            l8: temp := temp \div 10;
        };
        
        l9: if (n = sum) print << n, " is an Armstrong number" >> else print << n, "is not an Armstrong number" >>;
    }
}
*)
----------------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES n, sum, temp, remainder, digits, pc

vars == << n, sum, temp, remainder, digits, pc >>

Init == (* Global variables *)
        /\ n = N
        /\ sum = 0
        /\ temp = defaultInitValue
        /\ remainder = defaultInitValue
        /\ digits = 0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ temp' = n
      /\ pc' = "l1"
      /\ UNCHANGED << n, sum, remainder, digits >>

l1 == /\ pc = "l1"
      /\ IF temp # 0
            THEN /\ pc' = "l2"
            ELSE /\ pc' = "l4"
      /\ UNCHANGED << n, sum, temp, remainder, digits >>

l2 == /\ pc = "l2"
      /\ digits' = digits + 1
      /\ pc' = "l3"
      /\ UNCHANGED << n, sum, temp, remainder >>

l3 == /\ pc = "l3"
      /\ temp' = (temp \div 10)
      /\ pc' = "l1"
      /\ UNCHANGED << n, sum, remainder, digits >>

l4 == /\ pc = "l4"
      /\ temp' = n
      /\ pc' = "l5"
      /\ UNCHANGED << n, sum, remainder, digits >>

l5 == /\ pc = "l5"
      /\ IF temp # 0
            THEN /\ pc' = "l6"
            ELSE /\ pc' = "l9"
      /\ UNCHANGED << n, sum, temp, remainder, digits >>

l6 == /\ pc = "l6"
      /\ remainder' = temp % 10
      /\ pc' = "l7"
      /\ UNCHANGED << n, sum, temp, digits >>

l7 == /\ pc = "l7"
      /\ sum' = sum + remainder ^ digits
      /\ pc' = "l8"
      /\ UNCHANGED << n, temp, remainder, digits >>

l8 == /\ pc = "l8"
      /\ temp' = (temp \div 10)
      /\ pc' = "l5"
      /\ UNCHANGED << n, sum, remainder, digits >>

l9 == /\ pc = "l9"
      /\ IF n = sum
            THEN /\ PrintT(<< n, " is an Armstrong number" >>)
            ELSE /\ PrintT(<< n, "is not an Armstrong number" >>)
      /\ pc' = "Done"
      /\ UNCHANGED << n, sum, temp, remainder, digits >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6 \/ l7 \/ l8 \/ l9
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
    \* No post condition to assert, this program
    \* does not compute any result
    /\ TRUE

safety_partial_correctness ==
    /\ pc = "Done" 
        => post_condition

(* Invariant *)
\* Local invariant for each pc
Il0 ==
    pc = "l0" =>
        /\ n = N
        /\ sum = 0
        /\ temp = defaultInitValue
        /\ remainder = defaultInitValue
        /\ digits = 0

Il1 ==
    pc = "l1" =>
        /\ temp <= n
        /\ temp >= 0

Il2 ==
    pc = "l2" =>
        /\ temp # 0

Il3 ==
    pc = "l3" =>
        \* Assert an increment on `digits`
        /\ TRUE

Il4 ==
    pc = "l4" =>
        /\ temp = 0

Il5 ==
    pc = "l5" =>
        /\ temp <= n
        /\ temp >= 0

Il6 ==
    pc = "l6" =>
        /\ temp # 0

Il7 ==
    pc = "l7" =>
        /\ remainder = temp % 10

Il8 ==
    pc = "l8" =>
        \* Assert an increment on `sum`
        /\ TRUE

Il9 ==
    pc = "l9" =>
        /\ temp = 0

\* Global invariant
i ==
    /\ pc \in {"l0", "l1", "l2", "l3", "l4",
        "l5", "l6", "l7", "l8", "l9", "Done"}
    /\ Il0 /\ Il1 /\ Il2 /\ Il3 /\ Il4
    /\ Il5 /\ Il6 /\ Il7 /\ Il8 /\ Il9

(* Global check *)
check ==
    /\ i
    /\ safety_partial_correctness
    /\ safety_runtime

=============================================================================
\* Modification History
\* Last modified Sat Feb 22 11:39:23 CET 2020 by Default
\* Last modified Sat Feb 22 11:20:49 CET 2020 by Default
\* Last modified Thu Feb 20 18:19:52 CET 2020 by Default
\* Last modified Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
\* Created Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
