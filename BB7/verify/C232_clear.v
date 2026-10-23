From BB7 Require Import Individual72 C232_rules1 C232_rules2 C232_rules3 Clr.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Clearing on the machine *)
Lemma repeat_snoc : forall (x : nat) n Us, repeat x n ++ x :: Us = repeat x (S n) ++ Us.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma CH : forall v Us B, Kc (v :: Us) 0 B -->* Kc (O :: Us) 0 (iter v (U 0) B).
Proof.
  induction v; intros Us B.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, R2 |].
    eapply evstep_trans; [apply R1ITER |].
    rewrite iter_S', U_0. replace (0 + 3 * (B + 3)) with (3 * B + 9) by lia.
    apply IHv.
Qed.

Definition CDPst (m : nat) : Prop := forall v Us B, m <= B ->
  Kc (repeat O m ++ v :: Us) 0 B -->* Kc (repeat O (S m) ++ Us) 0 (iter v (U m) B).

(** clearing 1^i, v (depths 0..i) from counter B, given clearing at every depth <= i *)
Lemma CLW_gen : forall i, (forall m, m <= i -> CDPst m) ->
  forall q m v Us B, m + q = i ->
  Kc (repeat O m ++ repeat 1%nat q ++ v :: Us) 0 (W m B) -->*
  Kc (repeat O (S i) ++ Us) 0 (iter v (U i) (W i B)).
Proof.
  intros i Hc. induction q; intros m v Us B Hmq.
  - replace m with i by lia. simpl repeat. simpl app.
    pose proof (Hc i ltac:(lia) v Us (W i B)) as HH. unfold CDPst in HH. simpl repeat in HH. simpl app in HH.
    exact (HH ltac:(pose proof (W_ge i B); lia)).
  - simpl repeat. simpl app.
    eapply evstep_trans; [apply (Hc m ltac:(lia) 1%nat (repeat 1%nat q ++ v :: Us) (W m B)) |].
    + pose proof (W_ge m B). lia.
    + simpl iter. rewrite <- W_S. apply (IHq (S m) v Us B). lia.
Qed.

Lemma CDP_all : forall i, forall m, m <= i -> CDPst m.
Proof.
  induction i as [| i IH]; intros m Hm.
  - replace m with O by lia. intros v Us B _. simpl. apply CH.
  - destruct (Nat.le_gt_cases m i) as [Hle | Hgt]; [apply IH; exact Hle |].
    replace m with (S i) by lia. clear m Hm Hgt.
    intro v. induction v as [| w IHw]; intros Us B HB.
    + simpl iter. rewrite repeat_snoc. apply evstep_refl.
    + eapply evstep_trans; [apply progress_evstep, (R3 i w Us B HB) |].
      eapply evstep_trans; [apply R1ITER |]. simpl (O + 3 * 1).
      pose proof (CLW_gen i IH i 0 (B + 2 - i) (w :: Us) 3 ltac:(lia)) as H.
      rewrite W_0 in H. simpl app in H. simpl repeat in H.
      eapply evstep_trans; [exact H |].
      rewrite <- U_S.
      eapply evstep_trans; [apply (IHw Us (U (S i) B)) |].
      * pose proof (U_ge (S i) B). lia.
      * rewrite iter_S'. apply evstep_refl.
Qed.

Lemma CDP : forall m, CDPst m.
Proof. intros. apply (CDP_all m m). lia. Qed.

(** clearing a list of ones completely *)
Lemma clear_ones : forall i B,
  Kc (repeat 1%nat (S i)) 0 B -->* Kc (repeat O (S i)) 0 (W (S i) B).
Proof.
  intros.
  pose proof (CLW_gen i (fun m _ => CDP m) i 0 1 [] B ltac:(lia)) as H.
  rewrite W_0 in H. simpl app in H. rewrite repeat_snoc, !app_nil_r in H.
  simpl iter in H. rewrite <- W_S in H. exact H.
Qed.
