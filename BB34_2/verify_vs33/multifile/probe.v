(** Probe for the comparison hydra34 vs hydra33 (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).
    Prints the statements of the comparison theorems and checks that they use no axioms.  The machine files here
    are byte-identical copies of ../../verify/multifile and of the published hydra33 files (share_check.sh), so
    the theorems are about the published machines. *)

From BB8 Require BB33_upper BB34_vs_BB33 HydraUpper.
From BB8 Require BB33_halt BB34_bound.

Print BB33_upper.halts_with.

Check HydraUpper.chop_exact.
Check BB33_upper.upper_bound.
Check BB33_upper.halts_with_upper.
Check BB33_upper.score_window.
Check BB34_vs_BB33.cmp_33_34.
Check BB34_vs_BB33.BB34_beats_BB33.

Print Assumptions HydraUpper.chop_exact.
Print Assumptions BB33_upper.upper_bound.
Print Assumptions BB33_upper.halts_with_upper.
Print Assumptions BB33_upper.score_window.
Print Assumptions BB34_vs_BB33.cmp_33_34.
Print Assumptions BB34_vs_BB33.BB34_beats_BB33.
