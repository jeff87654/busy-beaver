(** Re-check the statements of the three theorem files and print their assumptions.
    Expected: five times "Closed under the global context". *)
From BB8 Require Import Individual82.
From BB8 Require BB8_champ35_1RB0RA BB8_champ35_bound BB8_champ35_exact.
Print BB8_champ35_1RB0RA.tm.
Check (BB8_champ35_1RB0RA.halt : halts BB8_champ35_1RB0RA.tm c0).
Check (BB8_champ35_bound.sigma_lower_bound : exists c N, c0 -[ BB8_champ35_1RB0RA.tm ]->* c /\ halted BB8_champ35_1RB0RA.tm c /\ BB8_champ35_bound.ones c N /\ BB8_champ35_bound.arrow 11 2 (BB8_champ35_bound.arrow 11 2 3) < N).
Check (BB8_champ35_bound.sigma_lower_bound_strong : exists c N, c0 -[ BB8_champ35_1RB0RA.tm ]->* c /\ halted BB8_champ35_1RB0RA.tm c /\ BB8_champ35_bound.ones c N /\ BB8_champ35_bound.arrow 35 2 (BB8_champ35_bound.arrow 35 2 3) < N).
Check (BB8_champ35_exact.bf_closed : 2 * BB8_champ35_bound.bf + 4 = BB8_champ35_bound.arrow 37 2 3).
Check (BB8_champ35_exact.score_closed : exists c, c0 -[ BB8_champ35_1RB0RA.tm ]->* c /\ halted BB8_champ35_1RB0RA.tm c /\ BB8_champ35_bound.ones c (12 * BB8_champ35_bound.arrow 37 2 3 + 58)).
Print BB8_champ35_bound.arrow.
Print BB8_champ35_bound.ones.
Print Assumptions BB8_champ35_1RB0RA.halt.
Print Assumptions BB8_champ35_bound.sigma_lower_bound.
Print Assumptions BB8_champ35_bound.sigma_lower_bound_strong.
Print Assumptions BB8_champ35_exact.bf_closed.
Print Assumptions BB8_champ35_exact.score_closed.
