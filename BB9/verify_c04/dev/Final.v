(** * Final.v : C04 halts from the blank tape (no premises).
    C04 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.
    Endgame.c04_halts_from_k31 (cascade + keys 37/43/49/55) applied to K31.K31_End.k31_end (key 31, agent c04-k31). *)
From BB8 Require Import Individual92.
From Dev Require Import Base Lift Endgame.
From K31 Require Import K31_End.

Theorem c04_halts : halts tm c0.
Proof.
  apply c04_halts_from_k31.
  intros t P s y l HP.
  destruct (k31_end t P s y l HP) as [c [Rl [H1 [H2 _]]]].
  exists c. split; assumption.
Qed.

Print Assumptions c04_halts.
