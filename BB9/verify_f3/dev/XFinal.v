(** * XFinal.v : the auxiliary machine X halts from the blank tape (bb9_f3_coq).
    XTop.reach_topX (X's own top: P1, P2, P3) + C04's cascade and endgame (Endgame.halts_from_reach, generalized over
    the parked-count margin Pm) + C04's key-31 endgame (K31_End.k31_end). *)
From XL Require Import Individual112.
From XDev Require Import Base Lift Step Fin Endgame XTop.
From XK31 Require Import K31_End.

Theorem x_halts : halts tm c0.
Proof.
  destruct L1x_props as [H60 [H2 H3]].
  eapply (halts_from_reach Pmx Pmx_ge); [| exact H60 | exact H2 | exact H3 | exact (reachF_P _ _ reach_topX)].
  intros t P s y l HP.
  destruct (k31_end t P s y l HP) as [c [Rl [H1 [H4 _]]]].
  exists c. split; assumption.
Qed.

Print Assumptions x_halts.
