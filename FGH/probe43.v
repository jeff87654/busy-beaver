(** Probe for FGH_BB43.v (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 -Q ../BB43/verify TM43 probe43.v).
    Prints the definitions and statements and checks that the theorems use no axioms. *)

From BB8 Require Ord KnuthFGH FGH_BB43.
From TM43 Require BB43_run BB43_score.

Print TM43.BB43_run.sigma.

Check TM43.BB43_score.sigma_bounds.
Check FGH_BB43.bb43_fgh.

Print Assumptions TM43.BB43_score.sigma_bounds.
Print Assumptions FGH_BB43.bb43_fgh.
