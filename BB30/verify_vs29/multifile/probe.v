(** Probe for the comparison hydra30 vs hydra29 (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).
    Prints the statements of the comparison theorems and checks that they use no axioms.  The machine files here
    are byte-identical copies of ../../verify/multifile and of the published hydra29 files (share_check.sh), so
    the theorems are about the published machines. *)

From BB8 Require BB29_upper BB30_vs_BB29 BB29_bound BB30_bound.

Print BB29_upper.halts_with.

Check BB29_upper.T4_upper.
Check BB29_upper.T4_lt_w9.
Check BB29_upper.halts_with_exact.
Check BB29_upper.halts_with_upper.
Check BB30_vs_BB29.BB30_beats_BB29.

Print Assumptions BB29_upper.T4_upper.
Print Assumptions BB29_upper.T4_lt_w9.
Print Assumptions BB29_upper.halts_with_exact.
Print Assumptions BB29_upper.halts_with_upper.
Print Assumptions BB30_vs_BB29.BB30_beats_BB29.
