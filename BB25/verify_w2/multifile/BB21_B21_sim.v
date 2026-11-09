(** B21: the abstract block machine is simulated by the TM. *)
From BB8 Require Import Individual212.
From BB8 Require Import BB21_B21_absdef BB21_B21_tm.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".

Lemma all1_repeat : forall b, all1 b = true -> b = repeat 1%nat (length b).
Proof.
  unfold all1. induction b as [| d b IH]; simpl; intros H; [reflexivity |].
  apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. subst. rewrite <- IH by exact H2. reflexivity.
Qed.

Lemma lsplit_spec : forall l p r, lsplit l = (p, r) -> l = repeat 1%nat p ++ r.
Proof.
  induction l as [| d l IH]; intros p r H; simpl in H.
  - inversion H; subst. reflexivity.
  - destruct d as [| [| d]].
    + inversion H; subst. reflexivity.
    + destruct (lsplit l) as [p' r'] eqn:E. inversion H; subst. simpl. rewrite (IH p' r eq_refl). reflexivity.
    + inversion H; subst. reflexivity.
Qed.

Lemma half : forall k, (2 * k / 2 = k)%nat.
Proof. intros. rewrite Nat.mul_comm. apply Nat.div_mul. lia. Qed.

Definition nz (ms : list nat) := Forall (fun m => m <> 0%nat) ms.

Lemma sweep_E_eq : forall x ms b R, all1 b && (2 <=? length b) = true ->
  sweep x ms (b :: R) = sweep (x + 2) (pred (length b) :: ms) R.
Proof. intros. cbn [sweep]. rewrite H. reflexivity. Qed.

Definition SimOK (x : nat) (ms : list nat) (R : list (list nat)) : Prop :=
  and (forall bs', sweep x ms R = Next bs' -> JC x ms (rb R (const 0)) -->* AT bs')
      (sweep x ms R = Halt -> exists c, and (JC x ms (rb R (const 0)) -->* c) (halted tm c)).

Lemma sweep_sim : forall R x ms, (1 <= x)%nat -> nz ms -> ms <> [] -> SimOK x ms R.
Proof.
  induction R as [| b R IH]; intros x ms Hx Hms Hne.
  - split; intros; discriminate.
  - destruct (all1 b && (2 <=? length b)) eqn:Eb.
    + pose proof (sweep_E_eq x ms b R Eb) as Hsw.
      apply andb_true_iff in Eb as [E1 E2]. apply Nat.leb_le in E2.
      apply all1_repeat in E1.
      destruct ms as [| m ms]; [congruence |].
      inversion Hms as [| ? ? Hm Hms']; subst. destruct m as [| m]; [congruence |].
      destruct x as [| x]; [lia |].
      destruct (length b) as [| [| n]] eqn:EL; [lia | lia |].
      assert (Hstep : JC (S x) (S m :: ms) (rb (b :: R) (const 0)) -->* JC (S x + 2) (S n :: S m :: ms) (rb R (const 0))).
      { rewrite E1. apply B_E. }
      destruct (IH (S x + 2)%nat (S n :: S m :: ms)) as [IH1 IH2]; [lia | constructor; [lia | constructor; [lia | exact Hms']] | discriminate |].
      simpl pred in Hsw. split.
      * intros bs' H. rewrite Hsw in H. follow Hstep. apply IH1. exact H.
      * intros H. rewrite Hsw in H. destruct (IH2 H) as [c [Hc Hh]]. exists c. split; [| exact Hh]. follow Hstep. exact Hc.
    + unfold SimOK. cbn [sweep]. rewrite Eb.
      destruct b as [| d T]; [split; intros; discriminate |].
      destruct d as [| [| d]].
      * split; intros; discriminate.
      * (* first digit 1 *)
        destruct T as [| t T].
        -- (* P *) destruct R as [| b2 R2].
           ++ destruct (x mod 4 =? 2)%nat eqn:E2.
              ** split; [intros; discriminate |]. intros _.
                 apply Nat.eqb_eq in E2. pose proof (Nat.div_mod x 4 ltac:(lia)) as Hd.
                 replace x with (4 * (x / 4) + 2)%nat by lia. apply B_halt. exact Hms.
              ** destruct ((x mod 4 =? 0) && (4 <=? x))%nat eqn:E0; [| split; intros; discriminate].
                 destruct ms as [| m ms]; [congruence |].
                 inversion Hms as [| ? ? Hm Hms']; subst. destruct m as [| m]; [congruence |].
                 split; [| intros; discriminate]. intros bs' H. injection H as <-.
                 apply andb_true_iff in E0 as [E0 E4]. apply Nat.eqb_eq in E0. apply Nat.leb_le in E4.
                 pose proof (Nat.div_mod x 4 ltac:(lia)) as Hd.
                 change (fst (Nat.divmod x 3 0 3)) with (x / 4)%nat.
                 destruct (x / 4)%nat as [| q] eqn:Eq; [lia |].
                 replace x with (4 * S q)%nat by lia. apply B_refill. exact Hms'.
           ++ destruct b2 as [| d2 T2]; [split; intros; discriminate |].
              destruct d2 as [| [| [| d2]]]; try (split; intros; discriminate).
              destruct T2 as [| t2 T2]; [| split; intros; discriminate].
              destruct (Nat.even x && (2 <=? x))%nat eqn:Ex; [| split; intros; discriminate].
              split; [| intros; discriminate]. intros bs' H. injection H as <-.
              apply andb_true_iff in Ex as [Ev E2]. apply Nat.leb_le in E2.
              apply Nat.even_spec in Ev as [k Hk]. subst x.
              change (fst (Nat.divmod (2 * k - 2) 1 0 1)) with ((2 * k - 2) / 2)%nat.
              replace (2 * k - 2)%nat with (2 * (k - 1))%nat by lia. rewrite half.
              replace (2 * k)%nat with (2 * (k - 1) + 2)%nat by lia.
              apply B_P. exact Hms.
        -- (* estep *) destruct (lsplit (t :: T)) as [p r] eqn:El.
           destruct r as [| e0 r]; [split; intros; discriminate |].
           destruct e0 as [| [| e]]; try (split; intros; discriminate).
           destruct ms as [| m ms]; [congruence |].
           inversion Hms as [| ? ? Hm Hms']; subst. destruct m as [| m]; [congruence |].
           destruct (1 <=? x)%nat eqn:E1; [| split; intros; discriminate].
           split; [| intros; discriminate]. intros bs' H. injection H as <-.
           apply lsplit_spec in El. rewrite El.
           destruct x as [| x]; [lia |]. replace (S x + 3)%nat with (x + 4)%nat by lia.
           apply B_est. exact Hms'.
      * (* decrement *)
        destruct (Nat.even x && (4 <=? x)) eqn:Ex; [| split; intros; discriminate].
        destruct ms as [| m ms]; [congruence |].
        inversion Hms as [| ? ? Hm Hms']; subst. destruct m as [| m]; [congruence |].
        split; [| intros; discriminate].
        intros bs' H. injection H as <-.
        apply andb_true_iff in Ex as [Ev E4]. apply Nat.leb_le in E4.
        apply Nat.even_spec in Ev as [k Hk].
        subst x. change (fst (Nat.divmod (2 * k - 4) 1 0 1)) with ((2 * k - 4) / 2)%nat.
        replace (2 * k - 4)%nat with (2 * (k - 2))%nat by lia. rewrite half.
        replace (2 * k)%nat with (2 * (k - 2) + 4)%nat by lia.
        apply B_dec. exact Hms'.
Qed.

Lemma forallb_nz : forall l, forallb (fun d => negb (d =? 0)%nat) l = true -> Forall (fun d => d <> 0%nat) l.
Proof.
  induction l as [| d l IH]; simpl; intros H; constructor.
  - apply andb_true_iff in H as [H _]. apply negb_true_iff in H. apply Nat.eqb_neq in H. exact H.
  - apply andb_true_iff in H as [_ H]. apply IH. exact H.
Qed.

Lemma astep_sim : forall bs,
  (forall bs', astep bs = Next bs' -> AT bs -->* AT bs') /\
  (astep bs = Halt -> exists c, (AT bs -->* c) /\ halted tm c).
Proof.
  intros bs. destruct bs as [| B0 R]; [split; intros; discriminate |].
  destruct B0 as [| x [| d ds]]; try (split; intros; discriminate).
  unfold astep. destruct (forallb (fun d => negb (d =? 0)%nat) (d :: ds)) eqn:Ed; [| split; intros; discriminate].
  apply forallb_nz in Ed.
  assert (He := B_engine x d ds R Ed).
  destruct (sweep_sim R (engf 0 (d :: ds) x + 3) [length (d :: ds)]) as [S1 S2];
    [lia | constructor; [simpl; lia | constructor] | discriminate |].
  split.
  - intros bs' H. follow He. apply S1. exact H.
  - intros H. destruct (S2 H) as [c [Hc Hh]]. exists c. split; [| exact Hh]. follow He. exact Hc.
Qed.

Inductive star : list (list nat) -> list (list nat) -> Prop :=
  | star_refl : forall b, star b b
  | star_step : forall b b' b'', astep b = Next b' -> star b' b'' -> star b b''.

Lemma star_sim : forall b b', star b b' -> AT b -->* AT b'.
Proof.
  intros b b' H. induction H.
  - finish.
  - destruct (astep_sim b) as [S1 _]. follow (S1 b' H). exact IHstar.
Qed.

Lemma halts_from : forall bs, star [[1%nat; 1%nat; 4%nat; 1%nat; 2%nat]; [1%nat]] bs -> astep bs = Halt -> halts tm c0.
Proof.
  intros bs Hs Hh. destruct (astep_sim bs) as [_ S2]. destruct (S2 Hh) as [c [Hc Hhc]].
  assert (Hall : c0 -->* c). { follow boot. follow (star_sim _ _ Hs). exact Hc. }
  destruct (with_counter Hall) as [n Hn].
  eapply halts_multistep; [| exact Hn]. apply halted_halts, Hhc.
Qed.

(** ** explicit halting configuration (for the score) *)
Lemma B_Es : forall E x m ms R, Forall (fun e => 2 <= e) E ->
  JC (S x) (S m :: ms) (rb (map (fun n => repeat 1%nat n) E ++ R) (const 0)) -->*
  JC (S x + 2 * length E) (rev (map pred E) ++ S m :: ms) (rb R (const 0)).
Proof.
  induction E as [| e E IH]; intros x m ms R HE; simpl.
  - replace (S (x + 0)) with (S x) by lia. finish.
  - inversion HE; subst. destruct e as [| [| n]]; [lia | lia |].
    follow (B_E x m ms n (map (fun n => repeat 1%nat n) E ++ R) (const 0)).
    replace (S x + 2) with (S (S (S x))) by lia.
    follow (IH (S (S x)) n (S m :: ms) R H2).
    apply evstep_refl'. f_equal; [lia | rewrite <- app_assoc; reflexivity].
Qed.

Lemma B_haltc : forall q ms, Forall (fun m => m <> 0%nat) ms ->
  JC (4 * q + 2) ms (rb [[1%nat]] (const 0)) -->* Halt_cfg (0 >> LP ms) ([1;1;0;0]^^(S q) *> 1 >> 1 >> const 0).
Proof.
  intros q ms Hms. destruct (LP_head ms Hms) as [l Hl].
  unfold JC. replace (4 * q + 2)%nat with (S (4 * q + 1)) by lia.
  simpl rb. simpl rl. rewrite Hl. follow J_P_raw.
  replace (4 * q + 1 + 3)%nat with (4 * S q)%nat by lia.
  apply refill_halt.
Qed.
