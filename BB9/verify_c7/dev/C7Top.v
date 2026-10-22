(** * C7Top.v : X' from the blank tape to the cascade moment at step 9 (L9 = 15u+17, u = 5jj+2), BB9/verify_c7.

    J1 (Abs.run_to_exhaustion) -> pa1, pa2 -> clear (R1) -> pb -> clear (R2) -> pa1, pa2 -> clear (R3) -> pb -> clear (R4)
    -> pa1, pc2 -> clear (R5) -> pd -> counter (2R5+3 rounds, R9) -> count_end (R10) -> entry1 -> sub3, sub0, sub3, sub4,
    sub0, sub0, sub3 -> D0f at L9.  All divisions are exact by C7Arith.c7_arith (every accumulator = rho mod Mres). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List ZArith.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift KStep Res C7Arith C7Phases C7PhB C7Count C7Casc C7Entry.
Opaque U arrow.
Local Open Scope nat_scope.

Lemma U_ge_j : forall j y, j + 2 <= U j y.
Proof.
  induction j as [| j IH]; intros y.
  - pose proof (U_lin 0 y). lia.
  - rewrite U_S. replace (2 * y + 2) with (S (S (2 * y))) by lia. cbn [iter].
    pose proof (IH (iter (2 * y) (U j) 0)). pose proof (U_lin j (U j (iter (2 * y) (U j) 0))). lia.
Qed.

Lemma iter_U_ge : forall v j x, 1 <= v -> j + 2 <= iter v (U j) x.
Proof. intros [| v] j x Hv; [lia |]. cbn [iter]. apply U_ge_j. Qed.

Lemma start_cfg : c0 -->* Kx (repeat 1 11) 1 (3 * Bx + 2) 0 e11.
Proof.
  eapply evstep_trans; [apply run_to_exhaustion |].
  unfold Kg. rewrite Kt_Kx, map_rep0, app_nil_r. apply evstep_refl.
Qed.

Lemma good_e1 : good e1.
Proof. left. eexists. reflexivity. Qed.
Lemma good_e11 : good e11.
Proof. left. eexists. reflexivity. Qed.
Lemma good_eC : good eC.
Proof. right. eexists. reflexivity. Qed.

(** one "PA + clear" stage: Kx(1^n;1;3R+2;t;e11) with x = 9R+n-20 = 5j -->* Kx(1^(3j+13) ++ [1]; 1; 3R'+2; 2+t; e1) *)
Lemma stageA : forall R n t j, 1 <= R -> 11 <= n -> 9 * R + n - 20 = 5 * j ->
  Kx (repeat 1 n) 1 (3 * R + 2) t e11 -->*
  Kx (repeat 1 (3 * j + 13) ++ [1]) 1 (3 * iter (j + 6) (U (3 * j + 12)) 0 + 2) (2 + t) e1.
Proof.
  intros R n t j HR Hn Hx.
  eapply evstep_trans; [apply progress_evstep, (pa1 R n t HR Hn) |]. rewrite Hx.
  eapply evstep_trans; [apply progress_evstep, pa2 |].
  replace (3 * j + 19) with (tokd (j + 6)) by (unfold tokd; lia).
  eapply evstep_trans; [apply (clear_dig (3 * j + 12) (j + 6) [1] (2 + t) e1 good_e1) |].
  replace (S (3 * j + 12)) with (3 * j + 13) by lia. apply evstep_refl.
Qed.

(** one "PB + clear" stage: Kx(1^n ++ [1];1;3R+2;t;e1) -->* Kx(1^(D+1);1;3R'+2;t;e11), D = 12R+n+4 *)
Lemma stageB : forall R n t, 1 <= R -> 11 <= n ->
  Kx (repeat 1 n ++ [1]) 1 (3 * R + 2) t e1 -->*
  Kx (repeat 1 (S (12 * R + n + 4))) 1 (3 * iter 2 (U (12 * R + n + 4)) 0 + 2) t e11.
Proof.
  intros R n t HR Hn.
  eapply evstep_trans; [apply progress_evstep, (pb R n t HR Hn) |].
  change 7 with (tokd 2).
  eapply evstep_trans; [apply (clear_dig _ 2 [] t e11 good_e11) |]. rewrite app_nil_r. apply evstep_refl.
Qed.


Definition R1 (j1 : nat) : nat := iter (j1 + 6) (U (3 * j1 + 12)) 0.
Definition D3 (j1 : nat) : nat := 12 * R1 j1 + 3 * j1 + 17.
Definition R2 (j1 : nat) : nat := iter 2 (U (D3 j1)) 0.
Definition R3 (j2 : nat) : nat := iter (j2 + 6) (U (3 * j2 + 12)) 0.
Definition D5 (j2 : nat) : nat := 12 * R3 j2 + 3 * j2 + 17.
Definition R4 (j2 : nat) : nat := iter 2 (U (D5 j2)) 0.
Definition R5 (j3 : nat) : nat := iter (j3 + 3) (U (3 * j3 + 21)) 0.
Definition R9 (j3 : nat) : nat := iter (2 * R5 j3 + 3) (U (S (3 * j3 + 19))) 0.
Definition R10 (j3 : nat) : nat := cend (3 * j3 + 19) (R9 j3).

(** j1 is fixed by Bx; given j1, j2 is fixed by R1, R2; given j2, j3 by R3, R4: the arithmetic lemma provides them. *)
Lemma reach_count : forall j1 j2 j3,
  9 * Bx = 5 * j1 + 9 -> 9 * R2 j1 + 12 * R1 j1 + 3 * j1 + 17 = 5 * j2 + 19 ->
  9 * R4 j2 + 12 * R3 j2 + 3 * j2 + 17 = 5 * j3 + 21 -> 1000 <= j1 ->
  c0 -->* Kx (repeat 1 (3 * j3 + 19)) 1 (3 * R10 j3 + 2) 6 (const S0).
Proof.
  intros j1 j2 j3 E1 E2 E3 Hj1.
  assert (HR1 : 1 <= R1 j1) by (unfold R1; apply iter_U_pos; lia).
  assert (HR2 : 1 <= R2 j1) by (unfold R2; apply iter_U_pos; lia).
  assert (HR3 : 1 <= R3 j2) by (unfold R3; apply iter_U_pos; lia).
  assert (HR4 : 1 <= R4 j2) by (unfold R4; apply iter_U_pos; lia).
  assert (HR5 : 1 <= R5 j3) by (unfold R5; apply iter_U_pos; lia).
  pose proof Bx_ge6 as HB.
  eapply evstep_trans; [apply start_cfg |].
  (* J1 -> J2 -> J3 *)
  eapply evstep_trans; [apply (stageA Bx 11 0 j1); lia |]. fold (R1 j1).
  eapply evstep_trans; [apply (stageB (R1 j1) (3 * j1 + 13) 2); lia |].
  replace (12 * R1 j1 + (3 * j1 + 13) + 4) with (D3 j1) by (unfold D3; lia). fold (R2 j1).
  (* J3 -> J4 -> J5 *)
  eapply evstep_trans; [apply (stageA (R2 j1) (S (D3 j1)) 2 j2); unfold D3 in *; lia |]. fold (R3 j2).
  eapply evstep_trans; [apply (stageB (R3 j2) (3 * j2 + 13) 4); lia |].
  replace (12 * R3 j2 + (3 * j2 + 13) + 4) with (D5 j2) by (unfold D5; lia). fold (R4 j2).
  (* J5 -> J6 : phase C *)
  eapply evstep_trans; [apply progress_evstep, (pa1 (R4 j2) (S (D5 j2)) 4); unfold D5; lia |].
  replace (9 * R4 j2 + S (D5 j2) - 20) with (5 * j3 + 2) by (unfold D5 in *; lia).
  eapply evstep_trans; [apply progress_evstep, pc2 |].
  replace (3 * j3 + 10) with (tokd (j3 + 3)) by (unfold tokd; lia).
  rewrite <- (app_nil_r (repeat 1 (3 * j3 + 21) ++ [tokd (j3 + 3)])), <- app_assoc. cbn [app].
  eapply evstep_trans; [apply (clear_dig (3 * j3 + 21) (j3 + 3) [] (2 + 4) eC good_eC) |].
  rewrite app_nil_r. fold (R5 j3). replace (S (3 * j3 + 21)) with (3 * j3 + 22) by lia.
  (* phase D and the counter *)
  eapply evstep_trans; [apply progress_evstep, (pd (R5 j3) (3 * j3 + 22) (2 + 4) HR5); lia |].
  replace (3 * j3 + 22 - 3) with (3 * j3 + 19) by lia.
  pose proof (count_loop (2 * R5 j3 + 3) (3 * j3 + 19) 0 (2 + 4) ltac:(lia)) as HC.
  replace (6 * 0 + 7) with 7 in HC by reflexivity.
  replace (3 + 3 * (2 * R5 j3 + 3)) with (6 * R5 j3 + 12) in HC by lia.
  eapply evstep_trans; [exact HC |].
  fold (R9 j3).
  eapply evstep_trans; [apply progress_evstep, (count_end (3 * j3 + 19) (R9 j3) (2 + 4)); lia |].
  fold (R10 j3). apply evstep_refl.
Qed.

(** finite far ends *)
Definition finl (l : side) : Prop := exists Ll : list Sym, l = Ll *> const S0.

Lemma finl_lnext : forall s y l, finl l -> finl (lnext s y l).
Proof.
  intros s y l [Ll ->]. exists ([S0;S1]^^y ++ [S1] ++ [S0;S1]^^s ++ [S1] ++ Ll). unfold lnext.
  rewrite !Str_app_assoc. reflexivity.
Qed.

Lemma finl_blank : finl (const S0).
Proof. exists (@nil Sym). reflexivity. Qed.

(** The cascade: entry (r = 1) and seven sub-steps r = 3, 0, 3, 4, 0, 0, 3, down to L9 = 15u + 17 (s = 2). *)
Lemma reach_L9 : forall m R J2 J3 J4 J5 J6 J7 J8 u, 1 <= R -> 10 <= m ->
  9 * m = 5 * J2 + 70 -> 3 * J2 + 35 = 5 * J3 + 60 -> 3 * J3 + 32 = 5 * J4 + 63 -> 3 * J4 + 35 = 5 * J5 + 64 ->
  3 * J5 + 32 = 5 * J6 + 60 -> 3 * J6 + 32 = 5 * J7 + 60 -> 3 * J7 + 32 = 5 * J8 + 63 -> 3 * J8 + 35 = 15 * u + 17 ->
  12 * R >= 40 ->
  exists l, finl l /\ Kx (repeat 1 (5 * m)) 1 (3 * R + 2) 6 (const S0) -->+ D0f 23 (15 * u + 17) (12 * R - 32) 2 (J8 + 13) l.
Proof.
  intros m R J2 J3 J4 J5 J6 J7 J8 u HR Hm E2 E3 E4 E5 E6 E7 E8 E9 HP.
  eexists. split.
  2:{
  eapply progress_trans; [apply (entry1 R m 6 HR Hm) |].
  replace (9 * m - 7) with (5 * J2 + 63) by lia.
  eapply progress_trans; [apply (sub3 J2 (12 * R + 4)); lia |].
  replace (3 * J2 + 35) with (5 * J3 + 60) by lia.
  eapply progress_trans; [apply (sub0 J3 (12 * R + 4 - 4)); lia |].
  replace (3 * J3 + 32) with (5 * J4 + 63) by lia.
  eapply progress_trans; [apply (sub3 J4 (12 * R + 4 - 4 - 6)); lia |].
  replace (3 * J4 + 35) with (5 * J5 + 64) by lia.
  eapply progress_trans; [apply (sub4 J5 (12 * R + 4 - 4 - 6 - 4)); lia |].
  replace (3 * J5 + 32) with (5 * J6 + 60) by lia.
  eapply progress_trans; [apply (sub0 J6 (12 * R + 4 - 4 - 6 - 4 - 6)); lia |].
  replace (3 * J6 + 32) with (5 * J7 + 60) by lia.
  eapply progress_trans; [apply (sub0 J7 (12 * R + 4 - 4 - 6 - 4 - 6 - 6)); lia |].
  replace (3 * J7 + 32) with (5 * J8 + 63) by lia.
  replace (12 * R - 32) with (12 * R + 4 - 4 - 6 - 4 - 6 - 6 - 6 - 4) by lia.
  replace (15 * u + 17) with (3 * J8 + 35) by lia.
  apply (sub3 J8 (12 * R + 4 - 4 - 6 - 4 - 6 - 6 - 6)). lia. }
  repeat apply finl_lnext. apply finl_blank.
Qed.
