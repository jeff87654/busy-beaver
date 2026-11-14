(** Probe for FGH_BB34.v (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 -Q ../BB34/verify TM34 probe34.v).
    Prints the definitions and statements and checks that the theorems use no axioms. *)

From BB8 Require Ord KnuthFGH FGH_BB34.
From TM34 Require BB34_run BB34_score.

Print Ord.FGH.
Print Ord.fin_fgh.
Print KnuthFGH.kn.
Print TM34.BB34_run.sigma.

Check KnuthFGH.fin_lower.
Check KnuthFGH.fin_upper.
Check KnuthFGH.fw_le_F.
Check KnuthFGH.window_kn6.
Check TM34.BB34_score.sigma_eq.
Check FGH_BB34.bb34_fgh.

Print Assumptions KnuthFGH.fin_lower.
Print Assumptions KnuthFGH.fin_upper.
Print Assumptions KnuthFGH.fw_le_F.
Print Assumptions KnuthFGH.window_kn6.
Print Assumptions TM34.BB34_score.sigma_eq.
Print Assumptions FGH_BB34.bb34_fgh.
