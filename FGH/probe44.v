(** Probe for FGH_BB44.v (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 -Q ../BB44/verify_44b Local probe44.v).
    Prints the definitions and statements and checks that the theorems use no axioms. *)

From BB8 Require Ord KnuthFGH FGH_BB44.
From Local Require BB44_run BB44A_run BB44B_run.

Print Local.BB44B_run.sigma.
Print Local.BB44A_run.sigma.
Print Local.BB44_run.sigma.

Check FGH_BB44.bb44B_fgh.
Check FGH_BB44.bb44A_fgh.
Check FGH_BB44.bb44C_fgh.

Print Assumptions FGH_BB44.bb44B_fgh.
Print Assumptions FGH_BB44.bb44A_fgh.
Print Assumptions FGH_BB44.bb44C_fgh.
