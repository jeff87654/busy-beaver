(** * 44-C against the previous BB(4,4) entry (loader3229's machine), in one statement.

    Loads both developments: this directory (logical path Local, 44-C, Argon's files) and ../verify (logical path
    TM44, loader3229's machine 0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA, MiniMax's files, PR #48).
    Both define the Knuth arrows by the same Fixpoint ([knuth_same] below); the published exact score of the old
    entry ([TM44.BB44_score.sigma_eq]: sigma = 2 ^(509 arrows) 3 + 510) is then below 44-C's sigma by Argon's
    [Local.BB44_bound.sigma_beats_official_bb44].  Both sigmas are the nonzero cells of the explicit final tapes
    ([final_cells_count] in each development).

    Compile after both directories:  coqc -Q $BUSYCOQ BusyCoq -Q ../verify TM44 -Q . Local BB44C_vs_loader3229.v *)

From TM44 Require BB44_run BB44_score.
From Local Require BB44_run BB44_bound.
From Coq Require Import PeanoNat Lia.

Lemma knuth_same : forall n a b, TM44.BB44_score.knuth n a b = Local.BB44_bound.knuth n a b.
Proof.
  induction n as [|n IH]; intros a b.
  - reflexivity.
  - simpl. induction b as [|b IHb].
    + reflexivity.
    + simpl. rewrite IHb, IH. reflexivity.
Qed.

(** loader3229's machine's exact sigma is below 44-C's. *)
Theorem beats_loader3229_exact : TM44.BB44_run.sigma < Local.BB44_run.sigma.
Proof.
  rewrite TM44.BB44_score.sigma_eq, knuth_same.
  exact Local.BB44_bound.sigma_beats_official_bb44.
Qed.

(** The same for the two final tapes (each development proves that its machine reaches the halting configuration
    whose nonzero cells are [final_cells]: [bb44_main] in ../verify, [bb44_new_champion_main] here). *)
Theorem beats_loader3229_score :
  length TM44.BB44_run.final_cells < length Local.BB44_run.final_cells.
Proof.
  rewrite TM44.BB44_run.final_cells_count, Local.BB44_run.final_cells_count.
  exact beats_loader3229_exact.
Qed.
