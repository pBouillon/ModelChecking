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
        l0: temp := n;
        
        l1: while (temp # 0)
        {
            l2: digits := digits + 1;
            l3: temp := temp / 10;
        }
        
        l4: temp := n;
        
        l5: while (temp # 0)
        {
            l6: remainder := temp % 10;
            l7: sum := sum; \* + power(remainder, digits);
            
            \* TODO: unwrap sum
            
            l8: temp := temp / 10;
        }
        
        l9: if (n = sum)
        {
            print << n, " is an Armstrong number" >>;
        }
        l10: else
        {
            print << n, "is not an Armstrong number" >>;
        }
    }
}
*)
----------------------------------------------------------------------------

\* BEGIN TRANSLATION


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
\* Last modified Thu Feb 20 18:19:52 CET 2020 by Default
\* Last modified Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
\* Created Fri Feb 20 18:08:42 CET 2020 by Pierre Bouillon
