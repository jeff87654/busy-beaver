(** * BB29: hydra-level rounds, the closed form W/T, and the processing lemma
      (BB29/analysis/REPORT.md sections 3c, 5 and 8.6-8.7). *)

From BB8 Require Import BB29_tm BB29_rules BB29_scan BB29_round.
From Coq Require Import Lia List PeanoNat.
Import ListNotations.
Set Default Goal Selector "!".

(** A height-3 hydra is a list of A-nodes; an A-node is the list of its B-children's leaf
    counts.  [Enc h w]: [w] encodes [h] with the marked node M somewhere on the rightmost path.
    Only the part up to the rightmost leaf's open bracket matters, followed by [j] closing
    brackets and the X of M (j = depth(rightmost leaf) - depth(M)). *)
Inductive Enc : list (list nat) -> list pr -> Prop :=
| Enc_A0 : forall hs j, Enc (hs ++ [[]]) (encH hs ++ [pO] ++ repeat pC j ++ [pX])
| Enc_B0 : forall hs A j, Enc (hs ++ [A ++ [0%nat]]) (encH hs ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX])
| Enc_L : forall hs A k j,
    Enc (hs ++ [A ++ [S k]]) (encH hs ++ [pO] ++ BB A ++ [pO] ++ leaf^^k ++ [pO] ++ repeat pC j ++ [pX]).

(** ** List algebra *)

Lemma BB_snoc : forall A k, BB (A ++ [k]) = BB A ++ Bk k.
Proof. intros. unfold BB. rewrite flat_map_app. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma BB_app : forall A1 A2, BB (A1 ++ A2) = BB A1 ++ BB A2.
Proof. intros. unfold BB. apply flat_map_app. Qed.

Lemma BB_repeat : forall k n, BB (repeat k n) = (Bk k)^^n.
Proof. induction n; [reflexivity|]. cbn [repeat lpow]. change (BB (k :: repeat k n)) with (Bk k ++ BB (repeat k n)). rewrite IHn. reflexivity. Qed.

Lemma encH_app : forall h1 h2, encH (h1 ++ h2) = encH h1 ++ encH h2.
Proof. intros. unfold encH. apply flat_map_app. Qed.

Lemma encH_repeat : forall A n, encH (repeat A n) = (encA A)^^n.
Proof. induction n; [reflexivity|]. cbn [repeat lpow]. change (encH (A :: repeat A n)) with (encA A ++ encH (repeat A n)). rewrite IHn. reflexivity. Qed.

Lemma leaves_BB : forall k, leaf^^k = BB (repeat 0%nat k).
Proof. induction k; [reflexivity|]. cbn [repeat lpow]. change (BB (0%nat :: repeat 0%nat k)) with (Bk 0 ++ BB (repeat 0%nat k)). rewrite <- IHk. reflexivity. Qed.

Lemma leaf_S : forall k, leaf^^(S k) = leaf^^k ++ [pO; pC].
Proof. intro k. cbn [lpow]. rewrite <- lpow_shift. reflexivity. Qed.

Ltac lsimpl := repeat rewrite <- app_assoc; cbn [app repeat]; reflexivity.

(** ** Inversion and construction of [Enc] *)

Lemma Enc_inv_nil : forall hs w, Enc (hs ++ [[]]) w -> exists j, w = encH hs ++ [pO] ++ repeat pC j ++ [pX].
Proof.
  intros hs w H. remember (hs ++ [[]]) as h eqn:Eh. destruct H as [hs' j|hs' A j|hs' A k j].
  - apply app_inj_tail in Eh as [-> _]. eauto.
  - apply app_inj_tail in Eh as [_ E]. destruct A; discriminate.
  - apply app_inj_tail in Eh as [_ E]. destruct A; discriminate.
Qed.

Lemma Enc_inv_0 : forall hs A w, Enc (hs ++ [A ++ [0%nat]]) w ->
  exists j, w = encH hs ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX].
Proof.
  intros hs A w H. remember (hs ++ [A ++ [0%nat]]) as h eqn:Eh. destruct H as [hs' j|hs' A' j|hs' A' k j].
  - apply app_inj_tail in Eh as [_ E]. destruct A; discriminate.
  - apply app_inj_tail in Eh as [-> E]. apply app_inj_tail in E as [-> _]. eauto.
  - apply app_inj_tail in Eh as [_ E]. apply app_inj_tail in E as [_ E]. discriminate.
Qed.

Lemma Enc_inv_S : forall hs A k w, Enc (hs ++ [A ++ [S k]]) w ->
  exists j, w = encH hs ++ [pO] ++ BB A ++ [pO] ++ leaf^^k ++ [pO] ++ repeat pC j ++ [pX].
Proof.
  intros hs A k w H. remember (hs ++ [A ++ [S k]]) as h eqn:Eh. destruct H as [hs' j|hs' A' j|hs' A' k' j].
  - apply app_inj_tail in Eh as [_ E]. destruct A; discriminate.
  - apply app_inj_tail in Eh as [_ E]. apply app_inj_tail in E as [_ E]. discriminate.
  - apply app_inj_tail in Eh as [-> E]. apply app_inj_tail in E as [-> E]. injection E as ->. eauto.
Qed.

Lemma Enc_A0' : forall hs j w, w = encH hs ++ [pO] ++ repeat pC j ++ [pX] -> Enc (hs ++ [[]]) w.
Proof. intros; subst; constructor. Qed.
Lemma Enc_B0' : forall hs A j w, w = encH hs ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX] -> Enc (hs ++ [A ++ [0%nat]]) w.
Proof. intros; subst; constructor. Qed.
Lemma Enc_L' : forall hs A k j w, w = encH hs ++ [pO] ++ BB A ++ [pO] ++ leaf^^k ++ [pO] ++ repeat pC j ++ [pX] ->
  Enc (hs ++ [A ++ [S k]]) w.
Proof. intros; subst; constructor. Qed.

(** M at depth 2 (a B node with k leaves). *)
Lemma Enc2 : forall hs A k, Enc (hs ++ [A ++ [k]]) (encH hs ++ [pO] ++ BB A ++ [pO] ++ leaf^^k ++ [pX]).
Proof.
  intros hs A [|k].
  - apply (Enc_B0' hs A 0). reflexivity.
  - apply (Enc_L' hs A k 1). rewrite leaf_S. lsimpl.
Qed.

(** M at depth 1 (an A node). *)
Lemma Enc1 : forall hs A, Enc (hs ++ [A]) (encH hs ++ [pO] ++ BB A ++ [pX]).
Proof.
  intros hs A. destruct A as [|k A _] using rev_ind.
  - apply (Enc_A0' hs 0). reflexivity.
  - rewrite BB_snoc. unfold Bk. destruct k as [|k].
    + apply (Enc_B0' hs A 1). lsimpl.
    + apply (Enc_L' hs A k 2). rewrite leaf_S. lsimpl.
Qed.

(** M = root (depth 0). *)
Lemma Enc0 : forall hs A, Enc (hs ++ [A]) (encH (hs ++ [A]) ++ [pX]).
Proof.
  intros hs A. rewrite encH_app. change (encH [A]) with (encA A ++ []). rewrite app_nil_r. unfold encA.
  destruct A as [|k A _] using rev_ind.
  - apply (Enc_A0' hs 1). lsimpl.
  - rewrite BB_snoc. unfold Bk. destruct k as [|k].
    + apply (Enc_B0' hs A 2). lsimpl.
    + apply (Enc_L' hs A k 3). rewrite leaf_S. lsimpl.
Qed.

(** ** The three composite rounds C(m) -> C(m+1) *)

(** Successor case: the rightmost leaf is a child of the root. *)
Lemma round_succ : forall m hs j, Cf m (encH hs ++ [pO] ++ repeat pC j ++ [pX]) -->+ Cf (S m) (encH hs ++ [pX]).
Proof.
  intros m hs j. unfold Cf.
  eapply progress_evstep_trans; [apply R2root|].
  apply (R1'_iter (S m) 0 hs).
Qed.

(** A-limit: a leaf B of an A node is removed; the shortened A ends up as m+3 copies. *)
Lemma round_A : forall m hs A j,
  Cf m (encH hs ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX]) -->+
  Cf (S m) (encH (hs ++ repeat A (S (S m))) ++ [pO] ++ BB A ++ [pX]).
Proof.
  intros m hs A j. unfold Cf.
  eapply progress_evstep_trans; [apply R2; oc|].
  replace (encH hs ++ [pO] ++ BB A ++ [pC; pO] ++ BB A ++ [pX]) with ((encH hs ++ [pO] ++ BB A ++ [pC]) ++ [pO] ++ BB A ++ [pX])
    by lsimpl.
  eapply evstep_trans; [apply (R1_iter (S m) 0); oc|].
  rewrite encH_app, encH_repeat. cbn [lpow]. unfold encA. rewrite <- !app_assoc. apply evstep_refl.
Qed.

(** B-limit: a leaf of a B node with k+1 leaves is removed; the shortened B ends up as m+3 copies. *)
Lemma round_B : forall m hs A k j,
  Cf m (encH hs ++ [pO] ++ BB A ++ [pO] ++ leaf^^k ++ [pO] ++ repeat pC j ++ [pX]) -->+
  Cf (S m) (encH hs ++ [pO] ++ BB (A ++ repeat k (S (S m))) ++ [pO] ++ leaf^^k ++ [pX]).
Proof.
  intros m hs A k j. unfold Cf.
  rewrite !leaves_BB.
  replace (encH hs ++ [pO] ++ BB A ++ [pO] ++ BB (repeat 0%nat k) ++ [pO] ++ repeat pC j ++ [pX])
    with ((encH hs ++ [pO] ++ BB A) ++ [pO] ++ BB (repeat 0%nat k) ++ [pO] ++ repeat pC j ++ [pX]) by lsimpl.
  eapply progress_evstep_trans; [apply R2; oc|].
  replace ((encH hs ++ [pO] ++ BB A) ++ [pO] ++ BB (repeat 0%nat k) ++ [pC; pO] ++ BB (repeat 0%nat k) ++ [pX])
    with (((encH hs ++ [pO] ++ BB A) ++ [pO] ++ BB (repeat 0%nat k) ++ [pC]) ++ [pO] ++ BB (repeat 0%nat k) ++ [pX]) by lsimpl.
  eapply evstep_trans; [apply (R1_iter (S m) 0); oc|].
  rewrite BB_app, (BB_repeat k (S (S m))). cbn [lpow]. unfold Bk. rewrite <- !leaves_BB. rewrite <- !app_assoc. apply evstep_refl.
Qed.

(** ** Closed form *)

(** T_0(phi)(m) = phi^(m+3)(m+1);  T_(k+1)(phi)(m) = (T_k)^(m+3)(phi)(m+1). *)
Fixpoint T (k : nat) (phi : nat -> nat) : nat -> nat :=
  match k with
  | O => fun m => Nat.iter (m + 3) phi (m + 1)
  | S k' => fun m => Nat.iter (m + 3) (T k') phi (m + 1)
  end.

(** W([]) = S;  W(A ++ [k]) = T_k(W(A)). *)
Definition W (A : list nat) : nat -> nat := fold_left (fun phi k => T k phi) A S.

Lemma W_nil : W [] = S.
Proof. reflexivity. Qed.

Lemma W_snoc : forall A k, W (A ++ [k]) = T k (W A).
Proof. intros. unfold W. rewrite fold_left_app. reflexivity. Qed.

Lemma W_rep : forall A k n, W (A ++ repeat k n) = Nat.iter n (T k) (W A).
Proof.
  intros A k n. induction n as [|n IH]; [rewrite app_nil_r; reflexivity|].
  rewrite repeat_snoc, app_assoc, W_snoc, IH. reflexivity.
Qed.

Lemma T0_eq : forall phi m, T 0 phi m = Nat.iter (S (S (S m))) phi (S m).
Proof. intros. cbn [T]. replace (m + 3) with (S (S (S m))) by lia. replace (m + 1) with (S m) by lia. reflexivity. Qed.

Lemma TS_eq : forall k phi m, T (S k) phi m = Nat.iter (S (S (S m))) (T k) phi (S m).
Proof. intros. cbn [T]. replace (m + 3) with (S (S (S m))) by lia. replace (m + 1) with (S m) by lia. reflexivity. Qed.

Global Opaque T W.

(** ** Processing lemma (structural induction; no ordinals) *)

Definition Good (A : list nat) : Prop :=
  forall hs m w, Enc (hs ++ [A]) w -> Cf m w -->* Cf (W A m) (encH hs ++ [pX]).

Lemma Good_nil : Good [].
Proof.
  intros hs m w H. destruct (Enc_inv_nil hs w H) as [j ->].
  rewrite W_nil. apply progress_evstep, round_succ.
Qed.

Lemma iterGood : forall A, Good A -> forall n hs x w, Enc (hs ++ repeat A n ++ [A]) w ->
  Cf x w -->* Cf (Nat.iter (S n) (W A) x) (encH hs ++ [pX]).
Proof.
  intros A HA n. induction n as [|n IH]; intros hs x w H.
  - apply HA. exact H.
  - eapply evstep_trans; [apply (HA (hs ++ repeat A (S n))); rewrite <- app_assoc; exact H|].
    rewrite (Nat.iter_succ_r (S n)).
    apply IH. rewrite repeat_snoc, (app_assoc hs (repeat A n) [A]). apply Enc0.
Qed.

Lemma Good_snoc0 : forall A, Good A -> Good (A ++ [0%nat]).
Proof.
  intros A HA hs m w H. destruct (Enc_inv_0 hs A w H) as [j ->].
  eapply evstep_trans; [apply progress_evstep, round_A|].
  rewrite W_snoc, T0_eq.
  apply (iterGood A HA (S (S m)) hs (S m)). rewrite app_assoc. apply Enc1.
Qed.

Lemma Good_rep : forall k, (forall A, Good A -> Good (A ++ [k])) -> forall A n, Good A -> Good (A ++ repeat k n).
Proof.
  intros k Pk A n HA. induction n as [|n IH]; [rewrite app_nil_r; exact HA|].
  rewrite repeat_snoc, app_assoc. apply Pk, IH.
Qed.

Lemma Good_snocS : forall k, (forall A, Good A -> Good (A ++ [k])) -> forall A, Good A -> Good (A ++ [S k]).
Proof.
  intros k Pk A HA hs m w H. destruct (Enc_inv_S hs A k w H) as [j ->].
  eapply evstep_trans; [apply progress_evstep, round_B|].
  rewrite W_snoc, TS_eq, <- W_rep.
  apply (Good_rep k Pk A (S (S (S m))) HA).
  rewrite (repeat_snoc k (S (S m))), app_assoc. apply Enc2.
Qed.

Lemma P_all : forall k A, Good A -> Good (A ++ [k]).
Proof.
  induction k as [|k IH].
  - apply Good_snoc0.
  - apply Good_snocS, IH.
Qed.

Theorem Good_all : forall A, Good A.
Proof.
  intro A. induction A as [|k A IH] using rev_ind; [apply Good_nil | apply P_all, IH].
Qed.

(** C(m, hs ++ [A], any marked depth) ->* C(W(A)(m), hs, 0). *)
Theorem process : forall hs A m w, Enc (hs ++ [A]) w -> Cf m w -->* Cf (W A m) (encH hs ++ [pX]).
Proof. intros. apply Good_all. assumption. Qed.
