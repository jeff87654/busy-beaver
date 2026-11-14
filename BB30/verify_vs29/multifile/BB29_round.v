(** * BB29: the configuration K(a,b,w) and the round lemmas R1, R1', R2, R3 (BB29/analysis/REPORT.md 3c). *)

From BB8 Require Import BB29_tm BB29_rules BB29_scan.
From Coq Require Import Lia List PeanoNat.
Import ListNotations.
Set Default Goal Selector "!".

(** [K a b w]: counter [O^a Z O^b] (head on the last pair, state P), then a separator Z, then
    the hydra word [w], then blank tape.  [w] is a word in tape order. *)
Definition K (a b : nat) (w : list pr) : Q * tape :=
  ls (const 0) (repeat pO a ++ [pZ] ++ repeat pO b) <{{qP}} rs (pZ :: w) (const 0).

(** Configuration just before a chop. *)
Definition Cf (m : nat) (w : list pr) : Q * tape := K m 0 w.

Lemma Kfin : forall a b w c, c = K a b w -> c -->* K a b w.
Proof. intros; subst; apply evstep_refl. Qed.

(** Shared prefixes: the P walk, [, and the V scan over the rest of the counter. *)
Lemma bstep_head : forall a b w,
  K a (S b) w -->+ ls (const 0) (repeat pO (S a) ++ [pZ] ++ repeat pO b ++ [pZ]) {{qN}}> rs w (const 0).
Proof.
  intros a b w. unfold K. rewrite !ls_app.
  eapply evstep_progress_trans; [apply Pwalk|].
  eapply progress_trans; [apply P_Z|].
  change (rs (repeat pO (S b)) ?r) with (rs [pO] (rs (repeat pO b) r)).
  eapply progress_trans; [apply LB_O|].
  change (rs (pZ :: w) ?r) with (rs [pZ] (rs w r)).
  eapply progress_evstep_trans; [apply VscanZ; oc|].
  rewrite repeat_snoc. fin.
Qed.

Lemma chop_head : forall a w,
  K a 0 w -->+ ls (const 0) (repeat pO (S a) ++ [pZ]) {{qV}}> rs w (const 0).
Proof.
  intros a w. unfold K. change (repeat pO 0) with (@nil pr). rewrite app_nil_r, ls_app.
  eapply progress_trans; [apply P_Z|].
  change (rs (pZ :: w) ?r) with (rs [pZ] (rs w r)).
  eapply progress_evstep_trans; [apply LB_Z|].
  rewrite repeat_snoc. fin.
Qed.

(** Splitting helpers for the left side *)
Lemma ls_split3 : forall l a b c, ls l (a ++ b ++ c) = ls (ls (ls l a) b) c.
Proof. intros. rewrite !ls_app. reflexivity. Qed.

(** R1: b-step with the marked node M at depth >= 1 (copy of M inserted before M). *)
Lemma R1 : forall a b pre A, OC pre ->
  K a (S b) (pre ++ [pO] ++ BB A ++ [pX]) -->+ K (S a) b (pre ++ [pO] ++ BB A ++ [pC; pO] ++ BB A ++ [pX]).
Proof.
  intros a b pre A Hpre.
  eapply progress_evstep_trans; [apply bstep_head|].
  replace (rs (pre ++ [pO] ++ BB A ++ [pX]) (const 0)) with (rs (pre ++ [pO] ++ BB A) (rs [pX] (const 0)))
    by (rewrite <- rs_app, <- !app_assoc; reflexivity).
  eapply evstep_trans; [apply progress_evstep, NscanX; oc|].
  rewrite ls_split3.
  eapply evstep_trans; [apply progress_evstep, S9a|].
  eapply evstep_trans; [apply progress_evstep, COPY; oc|].
  set (L2 := ls (const 0) (repeat pO (S a) ++ [pZ] ++ repeat pO b)).
  replace (ls (ls (const 0) (repeat pO (S a) ++ [pZ] ++ repeat pO b ++ [pZ])) pre) with (ls (ls L2 [pZ]) pre)
    by (unfold L2; rewrite <- !ls_app, <- !app_assoc; reflexivity).
  rewrite <- ls_app.
  eapply evstep_trans; [apply progress_evstep, RBscanZ; [oc | destruct pre; discriminate]|].
  unfold K, L2. fin.
Qed.

(** R1': b-step with M = root: nothing is copied. *)
Lemma R1' : forall a b hs, K a (S b) (encH hs ++ [pX]) -->+ K (S a) b (encH hs ++ [pX]).
Proof.
  intros a b hs.
  eapply progress_evstep_trans; [apply bstep_head|].
  rewrite rs_app.
  eapply evstep_trans; [apply progress_evstep, NscanX; oc|].
  set (L2 := ls (const 0) (repeat pO (S a) ++ [pZ] ++ repeat pO b)).
  replace (ls (const 0) (repeat pO (S a) ++ [pZ] ++ repeat pO b ++ [pZ])) with (ls L2 [pZ])
    by (unfold L2; rewrite <- !ls_app, <- !app_assoc; reflexivity).
  eapply evstep_trans; [apply progress_evstep, S9b|].
  unfold K, L2. fin.
Qed.

Lemma blank_after : forall j, rs (repeat pZ j) (rs [pZ] (const 0)) = const 0.
Proof. intro j. rewrite rs_Z0. apply rs_Z_const. Qed.

Lemma K0_left : forall a w, K 0 a w = ls (const 0) (repeat pO a) <{{qP}} rs (pZ :: w) (const 0).
Proof. intros a w. unfold K. cbn [repeat app ls]. rewrite Z_const. reflexivity. Qed.

(** Chop prefix: P, [, V scan to X, B erase back to the removed leaf's open bracket. *)
Lemma OC_repeatC : forall j, OC (repeat pC j).
Proof. induction j; simpl; [apply OC_nil | apply OC_cons; [apply isOC_C | assumption]]. Qed.
#[export] Hint Resolve OC_repeatC : ocdb.

Lemma chop_erase : forall a pre j, OC pre ->
  K a 0 (pre ++ [pO] ++ repeat pC j ++ [pX]) -->+
  ls (ls (const 0) (repeat pO (S a) ++ [pZ])) pre <{{qR}} rs [pX] (const 0).
Proof.
  intros a pre j Hpre.
  eapply progress_evstep_trans; [apply chop_head|].
  replace (rs (pre ++ [pO] ++ repeat pC j ++ [pX]) (const 0)) with (rs (pre ++ [pO] ++ repeat pC j) (rs [pX] (const 0)))
    by (rewrite <- rs_app, <- !app_assoc; reflexivity).
  eapply evstep_trans; [apply progress_evstep, VscanX; oc|].
  rewrite ls_split3.
  eapply evstep_trans; [apply progress_evstep, Berase|].
  rewrite blank_after. apply evstep_refl.
Qed.

(** R2, root case: the removed leaf was a child of the root. *)
Lemma R2root : forall a j hs,
  K a 0 (encH hs ++ [pO] ++ repeat pC j ++ [pX]) -->+ K 0 (S a) (encH hs ++ [pX]).
Proof.
  intros a j hs.
  eapply progress_evstep_trans; [apply chop_erase; oc|].
  rewrite ls_app.
  eapply evstep_trans; [apply progress_evstep, S9b|].
  rewrite K0_left. fin.
Qed.

(** R2, non-root case: the parent p (children [BB A]) becomes M and is copied once. *)
Lemma R2 : forall a j pre A, OC pre ->
  K a 0 (pre ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX]) -->+
  K 0 (S a) (pre ++ [pO] ++ BB A ++ [pC; pO] ++ BB A ++ [pX]).
Proof.
  intros a j pre A Hpre.
  replace (pre ++ [pO] ++ BB A ++ [pO] ++ repeat pC j ++ [pX]) with ((pre ++ [pO] ++ BB A) ++ [pO] ++ repeat pC j ++ [pX])
    by (rewrite <- !app_assoc; reflexivity).
  eapply progress_evstep_trans; [apply chop_erase; oc|].
  rewrite ls_split3.
  eapply evstep_trans; [apply progress_evstep, S9a|].
  eapply evstep_trans; [apply progress_evstep, COPY; oc|].
  rewrite (ls_app (repeat pO (S a)) [pZ]), <- (ls_app pre).
  eapply evstep_trans; [apply progress_evstep, RBscanZ; [oc | destruct pre; discriminate]|].
  rewrite K0_left. fin.
Qed.

(** R3: the empty hydra; the machine halts (B reads Z, B0 is undefined). *)
Definition c_end (a : nat) : Q * tape := ls (const 0) (repeat pO (S a) ++ [pZ]) <{{qB}} rs [pZ] (const 0).

Lemma R3 : forall a, K a 0 [pX] -->+ c_end a.
Proof.
  intros a. eapply progress_evstep_trans; [apply chop_head|].
  eapply evstep_trans; [apply progress_evstep, V_X|]. apply evstep_refl.
Qed.

Lemma c_end_halted : forall a, halted tm (c_end a).
Proof. intros a. unfold c_end. rewrite ls_snoc. apply (B_Z_halted (ls (const 0) (repeat pO (S a)))). Qed.

(** ** Iterated b-steps *)

Lemma R1_iter : forall b a pre A, OC pre ->
  K a b (pre ++ [pO] ++ BB A ++ [pX]) -->*
  K (a + b) 0 (pre ++ ([pO] ++ BB A ++ [pC])^^b ++ [pO] ++ BB A ++ [pX]).
Proof.
  induction b as [|b IH]; intros a pre A Hpre.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, R1; exact Hpre|].
    replace (pre ++ [pO] ++ BB A ++ [pC; pO] ++ BB A ++ [pX]) with ((pre ++ [pO] ++ BB A ++ [pC]) ++ [pO] ++ BB A ++ [pX])
      by (rewrite <- !app_assoc; reflexivity).
    eapply evstep_trans; [apply IH; oc|].
    replace (S a + b) with (a + S b) by lia. cbn [lpow]. rewrite <- !app_assoc. apply evstep_refl.
Qed.

Lemma R1'_iter : forall b a hs, K a b (encH hs ++ [pX]) -->* K (a + b) 0 (encH hs ++ [pX]).
Proof.
  induction b as [|b IH]; intros a hs.
  - rewrite Nat.add_0_r. apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, R1'|].
    replace (a + S b) with (S a + b) by lia. apply IH.
Qed.
