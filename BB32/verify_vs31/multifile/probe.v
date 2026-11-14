(** Probe for the comparison hydra32 vs hydra31 (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).
    Prints the statements of the comparison theorems and checks that they use no axioms.  The machine files here
    are byte-identical copies of ../../verify/multifile and of the published hydra31 files (share_check.sh), so
    the theorems are about the published machines. *)

From BB8 Require BB31_upper BB32_vs_BB31 HydraUpper.
From BB8 Require BB31_halt BB32_bound.

Print BB31_upper.halts_with.

Check HydraUpper.chop_exact.
Check BB31_upper.upper_bound.
Check BB31_upper.halts_with_upper.
Check BB31_upper.score_window.
Check BB32_vs_BB31.cmp_31_32.
Check BB32_vs_BB31.BB32_beats_BB31.

Print Assumptions HydraUpper.chop_exact.
Print Assumptions BB31_upper.upper_bound.
Print Assumptions BB31_upper.halts_with_upper.
Print Assumptions BB31_upper.score_window.
Print Assumptions BB32_vs_BB31.cmp_31_32.
Print Assumptions BB32_vs_BB31.BB32_beats_BB31.
