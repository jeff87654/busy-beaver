(** Probe for 53-Main's comparisons (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q ../verify Local -Q ../../BB43/verify TM43 -Q . BB8 probe.v).
    Prints the statements and checks that they use no axioms. *)

From BB8 Require Ord BB53_vs_BB43 BB53_fgh.
From TM43 Require BB43_run BB43_score.
From Local Require BB53_run BB53_bound.

Print Ord.FGH.
Print Ord.fin_fgh.
Print Local.BB53_bound.f_omega.
Check TM43.BB43_score.sigma_bounds.

Check BB53_vs_BB43.knuth_same.
Check BB53_vs_BB43.BB53_beats_BB43.
Check BB53_fgh.fin_fgh_le_knuth.
Check BB53_fgh.FGH_omega_le_home.
Check BB53_fgh.sigma_exceeds_FGH.

Print Assumptions BB53_vs_BB43.knuth_same.
Print Assumptions BB53_vs_BB43.BB53_beats_BB43.
Print Assumptions BB53_fgh.fin_fgh_le_knuth.
Print Assumptions BB53_fgh.FGH_omega_le_home.
Print Assumptions BB53_fgh.sigma_exceeds_FGH.
