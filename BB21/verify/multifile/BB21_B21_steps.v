(** B21: the abstract machine on states decomposed as  b0 | E's | frontier | blocks above. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef.
Import ListNotations.
Set Default Goal Selector "!".

Definition ones (n : nat) : list nat := repeat 1 n.
Definition isE (b : list nat) : bool := all1 b && (2 <=? length b).

Record st := mk { b0 : list nat; es : list nat; fr : list nat; up : list (list nat) }.

(** es is nearest-first: the E just below the frontier comes first *)
Definition enc (s : st) : list (list nat) := b0 s :: rev (map ones (es s)) ++ fr s :: up s.

Definition eng (b : list nat) : nat :=
  match b with
  | x :: d :: ds => engf 0 (d :: ds) x
  | _ => 0
  end.

Lemma all1_ones : forall n, all1 (ones n) = true.
Proof. induction n; simpl; [reflexivity |]. exact IHn. Qed.

Lemma isE_ones : forall n, 2 <= n -> isE (ones n) = true.
Proof. intros. unfold isE. rewrite all1_ones. unfold ones. rewrite repeat_length. rewrite (proj2 (Nat.leb_le 2 n) H). reflexivity. Qed.

Section Generic.
Variable refill : nat -> list nat -> res.

Lemma sweep_pass : forall E x ms R, Forall (fun e => 2 <= e) E ->
  sweepG refill x ms (map ones E ++ R) = sweepG refill (x + 2 * length E) (rev (map pred E) ++ ms) R.
Proof.
  induction E as [| e E IH]; intros x ms R HE; cbn [map app length].
  - rewrite Nat.add_0_r. reflexivity.
  - inversion HE; subst. pose proof (isE_ones e H1) as Q. unfold isE in Q.
    cbn [sweepG]. rewrite Q.
    rewrite IH by assumption. unfold ones. rewrite repeat_length.
    cbn [rev map]. rewrite <- app_assoc. simpl. f_equal. lia.
Qed.

Ltac shw := match goal with |- ?g => idtac g end.

Definition nzd (b : list nat) := Forall (fun d => d <> 0) b.
Definition b0ok (b : list nat) := exists x d ds, b = x :: d :: ds /\ nzd (d :: ds).
Definition esok (es : list nat) := Forall (fun e => 2 <= e) es.

Definition jacc (s : st) : nat := eng (b0 s) + 3 + 2 * length (es s).

Lemma forallb_nzd : forall l, nzd l -> forallb (fun d => negb (d =? 0)) l = true.
Proof.
  induction l as [| d l IH]; simpl; intros H; [reflexivity |].
  inversion H; subst. apply andb_true_iff. split.
  - apply negb_true_iff. apply Nat.eqb_neq. exact H2.
  - apply IH. exact H3.
Qed.

Lemma astep_enc : forall s, b0ok (b0 s) -> esok (es s) ->
  astepG refill (enc s) = sweepG refill (jacc s) (map pred (es s) ++ [length (b0 s) - 1]) (fr s :: up s).
Proof.
  intros [b0' es' fr' up'] [x [d [ds [Hb Hnz]]]] Hes. simpl b0 in Hb. simpl es in Hes. subst b0'. unfold enc, astepG.
  simpl b0. simpl es. simpl fr. simpl up. cbv beta iota. rewrite (forallb_nzd _ Hnz).
  rewrite <- map_rev. rewrite sweep_pass by (apply Forall_rev; exact Hes).
  rewrite map_rev, rev_involutive, rev_length. unfold jacc, eng. simpl b0. simpl es. simpl length. reflexivity.
Qed.

Lemma restore_es : forall es n, restore (map pred es ++ [n]) = ones n :: rev (map ones (map pred es)).
Proof.
  intros. unfold restore. rewrite map_app. rewrite rev_app_distr. simpl. reflexivity.
Qed.

(** the sweep at the frontier, after the E's *)
Lemma sweep_front : forall x ms fr up, isE fr = false ->
  sweepG refill x ms (fr :: up) =
  match fr with
    | S (S d) :: T =>
        if Nat.even x && (4 <=? x) then
          match ms with
          | S m :: ms' => Next (restore ms' ++ (repeat 1 (S m) ++ Xl ((x - 4) / 2)) :: (S d :: T) :: up)
          | _ => Stuck
          end
        else Stuck
    | [1] =>
        match up with
        | [] => refill x ms
        | [2] :: R'' => if Nat.even x && (2 <=? x) then Next (restore ms ++ Xl ((x - 2) / 2) :: [1] :: R'') else Stuck
        | _ => Stuck
        end
    | 1 :: tl =>
        match lsplit tl, ms with
        | (p, S (S e) :: T), S m :: _ =>
            if 1 <=? x then Next (restore ms ++ (repeat 1 p ++ (x + 3) :: S e :: T) :: up) else Stuck
        | _, _ => Stuck
        end
    | _ => Stuck
  end.
Proof. intros. unfold isE in H. cbn [sweepG]. rewrite H. reflexivity. Qed.

Lemma isE_false_cons2 : forall d T, isE (S (S d) :: T) = false.
Proof. intros. reflexivity. Qed.

Lemma b0ok_len : forall b, b0ok b -> 2 <= length b.
Proof. intros b [x [d [ds [-> _]]]]. simpl. lia. Qed.

Lemma ms_head : forall es n, esok es -> 2 <= n -> exists m ms', map pred es ++ [n - 1] = S m :: ms'.
Proof.
  intros [| e es] n Hes Hn; simpl.
  - exists (n - 2), []. f_equal. lia.
  - inversion Hes; subst. exists (e - 2), (map pred es ++ [n - 1]). f_equal. lia.
Qed.

Lemma enc_restore : forall n es fr up,
  restore (map pred es ++ [n]) ++ fr :: up = enc (mk (ones n) (map pred es) fr up).
Proof. intros. rewrite restore_es. unfold enc. simpl. reflexivity. Qed.

Lemma lsplit_spec : forall l p r, lsplit l = (p, r) -> l = repeat 1 p ++ r.
Proof.
  induction l as [| d l IH]; intros p r H; simpl in H.
  - inversion H; subst. reflexivity.
  - destruct d as [| [| d]].
    + inversion H; subst. reflexivity.
    + destruct (lsplit l) as [p' r'] eqn:E. inversion H; subst. simpl. rewrite (IH p' r eq_refl). reflexivity.
    + inversion H; subst. reflexivity.
Qed.

Lemma all1_big : forall p e T, all1 (repeat 1 p ++ S (S e) :: T) = false.
Proof. induction p; intros; simpl. - reflexivity. - apply IHp. Qed.

Lemma step_est : forall s tl p e T, b0ok (b0 s) -> esok (es s) -> fr s = 1 :: tl ->
  lsplit tl = (p, S (S e) :: T) ->
  astepG refill (enc s) = Next (enc (mk (ones (length (b0 s) - 1)) (map pred (es s))
                              (repeat 1 p ++ (jacc s + 3) :: S e :: T) (up s))).
Proof.
  intros s tl p e T Hb Hes Hfr Hl. rewrite astep_enc by assumption.
  pose proof (lsplit_spec _ _ _ Hl) as Htl.
  assert (HE : isE (fr s) = false).
  { rewrite Hfr, Htl. unfold isE. simpl. rewrite all1_big. reflexivity. }
  rewrite (sweep_front _ _ _ _ HE). rewrite Hfr.
  destruct tl as [| t tl'].
  { simpl in Htl. destruct p; discriminate. }
  destruct (ms_head (es s) (length (b0 s)) Hes (b0ok_len _ Hb)) as [m [ms' Hms]].
  rewrite Hl, Hms.
  replace (1 <=? jacc s) with true by (symmetry; apply Nat.leb_le; unfold jacc; lia).
  rewrite <- Hms. f_equal. rewrite enc_restore. reflexivity.
Qed.

Lemma step_dec_es : forall s d T e es', b0ok (b0 s) -> esok (es s) -> fr s = S (S d) :: T -> es s = e :: es' ->
  Nat.even (jacc s) = true -> 4 <= jacc s ->
  astepG refill (enc s) = Next (enc (mk (ones (length (b0 s) - 1)) (map pred es')
                              (ones (pred e) ++ Xl ((jacc s - 4) / 2)) ((S d :: T) :: up s))).
Proof.
  intros s d T e es' Hb Hes Hfr Hee Hev H4. rewrite astep_enc by assumption.
  assert (HE : isE (fr s) = false) by (rewrite Hfr; reflexivity).
  rewrite (sweep_front _ _ _ _ HE). rewrite Hfr. rewrite Hev. replace (4 <=? jacc s) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Hee. simpl andb. rewrite Hee in Hes. inversion Hes; subst.
  destruct e as [| [| e]]; [lia | lia |]. simpl map at 1. cbn iota.
  f_equal. unfold enc. simpl. rewrite restore_es. simpl. f_equal. all: try (rewrite <- app_assoc; reflexivity).
Qed.

Lemma step_dec_0 : forall s d T, b0ok (b0 s) -> es s = [] -> fr s = S (S d) :: T ->
  Nat.even (jacc s) = true -> 4 <= jacc s ->
  astepG refill (enc s) = Next ((ones (length (b0 s) - 1) ++ Xl ((jacc s - 4) / 2)) :: (S d :: T) :: up s).
Proof.
  intros s d T Hb Hee Hfr Hev H4. rewrite astep_enc by (try assumption; rewrite Hee; constructor).
  assert (HE : isE (fr s) = false) by (rewrite Hfr; reflexivity).
  rewrite (sweep_front _ _ _ _ HE). rewrite Hfr. rewrite Hev. replace (4 <=? jacc s) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Hee. simpl. pose proof (b0ok_len _ Hb).
  destruct (length (b0 s)) as [| [| n]] eqn:L; [lia | lia |]. simpl. repeat f_equal. all: lia.
Qed.

Lemma step_P : forall s up', b0ok (b0 s) -> esok (es s) -> fr s = [1] -> up s = [2] :: up' ->
  Nat.even (jacc s) = true -> 2 <= jacc s ->
  astepG refill (enc s) = Next (enc (mk (ones (length (b0 s) - 1)) (map pred (es s)) (Xl ((jacc s - 2) / 2)) ([1] :: up'))).
Proof.
  intros s up' Hb Hes Hfr Hup Hev H2. rewrite astep_enc by assumption.
  assert (HE : isE (fr s) = false) by (rewrite Hfr; reflexivity).
  rewrite (sweep_front _ _ _ _ HE). rewrite Hfr, Hup, Hev. replace (2 <=? jacc s) with true by (symmetry; apply Nat.leb_le; lia).
  simpl andb. cbn iota. f_equal. rewrite enc_restore. reflexivity.
Qed.

End Generic.

(** ** B21's refill (the only refill-specific facts) *)
Lemma step_halt : forall s, b0ok (b0 s) -> esok (es s) -> fr s = [1] -> up s = [] ->
  jacc s mod 4 = 2 -> astepG refill21 (enc s) = Halt.
Proof.
  intros s Hb Hes Hfr Hup H. rewrite (astep_enc refill21) by assumption.
  assert (HE : isE (fr s) = false) by (rewrite Hfr; reflexivity).
  rewrite (sweep_front refill21 _ _ _ _ HE). rewrite Hfr, Hup. unfold refill21. rewrite H. reflexivity.
Qed.

Lemma step_refill : forall s e es', b0ok (b0 s) -> esok (es s) -> fr s = [1] -> up s = [] -> es s = e :: es' ->
  jacc s mod 4 = 0 -> 4 <= jacc s ->
  astepG refill21 (enc s) = Next (ones (length (b0 s) - 1) :: rev (map ones (map pred es')) ++
                        (ones (pred e) ++ [4; 1]) :: repeat [2] (jacc s / 4)).
Proof.
  intros s e es' Hb Hes Hfr Hup Hee H0 H4. rewrite (astep_enc refill21) by assumption.
  assert (HE : isE (fr s) = false) by (rewrite Hfr; reflexivity).
  rewrite (sweep_front refill21 _ _ _ _ HE). rewrite Hfr, Hup. unfold refill21. rewrite H0. simpl.
  replace (4 <=? jacc s) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Hee in Hes |- *. inversion Hes; subst. destruct e as [| [| e]]; [lia | lia |].
  simpl. rewrite restore_es. simpl. destruct (jacc s) as [| [| [| [| j]]]]; try lia. reflexivity.
Qed.
