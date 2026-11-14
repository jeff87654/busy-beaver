(** Probe for FGH_BB54.v (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 -Q ../BB54/verify_54l Local probe54.v).
    Prints the definitions and statements and checks that the theorems use no axioms. *)

From BB8 Require Ord KnuthFGH FGH_BB54.
From Local Require BB54_run BB54_bound.

Print Local.BB54_run.sigma.
Print Local.BB54_bound.f_omega1.

Check FGH_BB54.bb54_fgh.

Print Assumptions FGH_BB54.bb54_fgh.
