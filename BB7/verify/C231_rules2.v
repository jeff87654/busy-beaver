From BB7 Require Import Individual72 C231_rules1.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Lemma zsnoc : forall n (r : side), [0]^^n *> 0 >> r = 0 >> [0]^^n *> r.
Proof. intros. apply (align_lpow 0 [] r n). Qed.

Lemma MCS : forall q p r,
  const 0 {{E}}> 0 >> [1]^^p *> 0 >> 0 >> [1]^^q *> r -->*
  const 0 {{E}}> 0 >> [1]^^(3 * q + p) *> 0 >> 0 >> r.
Proof.
  induction q; intros.
  - finish.
  - change ([1]^^(S q) *> r) with (1 >> [1]^^q *> r).
    follow (progress_evstep _ _ _ (MC p ([1]^^q *> r))). follow (IHq (3 + p) r). finish.
Qed.

Fixpoint rgt (ds : list nat) : side :=
  match ds with
  | [] => 1 >> const 0
  | d :: t => [1]^^(2 * d) *> 0 >> 0 >> rgt t
  end.

Definition Kc (ds : list nat) (a b : nat) : Q * tape :=
  const 0 {{E}}> 0 >> [1]^^(S (2 * b)) *> 0 >> 0 >> [1]^^(2 * a) *> 0 >> 0 >> rgt ds.

Lemma R1ITER : forall a ds b, Kc ds a b -->* Kc ds 0 (b + 3 * a).
Proof.
  intros. unfold Kc.
  follow (MCS (2 * a) (S (2 * b)) (0 >> 0 >> rgt ds)).
  replace (3 * (2 * a) + S (2 * b)) with (S (2 * (b + 3 * a))) by lia.
  finish.
Qed.

Lemma START : forall p r,
  const 0 {{E}}> 0 >> [1]^^p *> 0 >> 0 >> 0 >> r -->+ (0 >> const 0) <{{F}} [1]^^(3 + p) *> 0 >> 0 >> r.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crF. ex.
Qed.

Lemma FW : forall l n r,
  (0 >> l) <{{F}} [1]^^(S (S n)) *> 0 >> 0 >> 0 >> r -->+ (0 >> 0 >> 1 >> l) <{{F}} [1]^^(S n) *> 0 >> 0 >> r.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crF. ex.
Qed.

Lemma FWS : forall j l n r,
  (0 >> l) <{{F}} [1]^^(j + S n) *> [0]^^(S (S j)) *> r -->*
  (0 >> [0;1]^^j *> l) <{{F}} [1]^^(S n) *> 0 >> 0 >> r.
Proof.
  induction j; intros.
  - finish.
  - replace (S j + S n) with (j + S (S n)) by lia.
    replace ([0]^^(S (S (S j))) *> r) with ([0]^^(S (S j)) *> 0 >> r)
      by (rewrite zsnoc; reflexivity).
    follow (IHj l (S n) (0 >> r)).
    follow (progress_evstep _ _ _ (FW ([0;1]^^j *> l) n r)). finish.
Qed.

Lemma TURN : forall l n r,
  (0 >> 0 >> 1 >> l) <{{F}} [1]^^(S (S n)) *> 0 >> 0 >> 1 >> 1 >> r -->+
  l <{{F}} 1 >> 0 >> [1]^^(5 + n) *> 0 >> 0 >> r.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crE. ex. follow crB. ex. follow crE. ex.
Qed.

Lemma BW : forall l T,
  (0 >> 1 >> 0 >> 1 >> l) <{{F}} 1 >> 0 >> T -->+ l <{{F}} 1 >> 0 >> 1 >> 1 >> 0 >> 0 >> T.
Proof. intros. eapply progress_intro; [prove_step | simpl_tape]. ex. Qed.

Lemma BWS : forall i l T,
  ([0;1;0;1]^^i *> l) <{{F}} 1 >> 0 >> T -->* l <{{F}} 1 >> 0 >> [1;1;0;0]^^i *> T.
Proof.
  induction i; intros.
  - finish.
  - change ([0;1;0;1]^^(S i) *> l) with (0 >> 1 >> 0 >> 1 >> [0;1;0;1]^^i *> l).
    follow (progress_evstep _ _ _ (BW ([0;1;0;1]^^i *> l) T)).
    follow (IHi l ([1;1;0;0] *> T)).
    rewrite lpow_shift'. finish.
Qed.

Lemma FINB : forall T, const 0 <{{F}} 1 >> 0 >> T -->+ const 0 {{E}}> 0 >> 1 >> 0 >> 0 >> T.
Proof. intros. eapply progress_intro; [prove_step | simpl_tape]. ex. Qed.
