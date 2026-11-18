(** * The run of 3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB, its halting configuration, and the score *)

(** Configurations (the same Ligocki family as BB34/BB73):
      B(k, n, m) R = 0^inf 1^(2m+1) 2^k B> 1^n R = [Bcfg k n m r].
    The 730-step start ends at
      B(2, 1, 0) 0^3 1^2 2^21 3 2 1 0^inf.
    The main rule [B_rule] and the descent [rule2] are exactly as in BB83.
    The tail automaton reads the markers after the 0-block:

      B(1,0,m) 0 0 r  -(rule3a)-> B(1,0,round m) 0 r            (one round)
      B(1,0,m) 0 1 r  -(rule3b)-> B(2,1,0) 0^(2m+3) r           (reset)
      B(1,0,m) 0 2 r  -(rule3c)-> B(2,1,0) 0^3 1^(2m+3) r      (new in BB74)
      B(1,0,m) 0 3 r  -(halt)->   F> 3                          (halt)

    [mfin] is sealed behind a [sig] exactly as in BB83. *)

From TM74 Require Import Individual74 BB74_rules BB74_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(2,1,0) 0^4 1^4 2 1 2] in 152 steps. *)

Lemma start_B : c0 -->* Bcfg 2 1 0 (0 >> 0 >> 0 >> 1 >> 1 >> [S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> (3 >> 2 >> 1 >> const 0)).
Proof.
  rewrite <- cfg_730_is_B.
  apply start_raw.
Qed.

(** ** [B_rule] with its result abstracted. *)

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** One step at level 1: [B(1,1,m) -> B(1,0,m+1)]. *)
Lemma B1_one : forall m r,
  Bcfg 1 1 m r -->* Bcfg 1 0 (m + 1) r.
Proof.
  intros m r.
  follow (B_rule 0 1 m r).
  rewrite iter_g0.
  apply evstep_refl'. reflexivity.
Qed.

(** ** The descent after rule 2 (identical to BB73). *)

Fixpoint desc (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => desc n' (g (S n') m)
  end.

Lemma rule2_step : forall j m r,
  Bcfg (S (S j)) 0 m (0 >> r) -->*
  Bcfg (S j) 0 (g (S j) m) (0 >> r).
Proof.
  intros j m r.
  follow (rule2 j m r).
  assert (HE : S (S (2 * m)) = 2 * m + 2) by lia.
  rewrite HE.
  apply (B_rule_gen j (2 * m + 2) 0%nat (0 >> r) (g (S j) m)).
  reflexivity.
Qed.

Lemma rule2_phase : forall n m r,
  Bcfg (S (S n)) 0 m (0 >> r) -->*
  Bcfg 1 0 (desc (S n) m) (0 >> r).
Proof.
  intros n. revert n.
  fix IH 1. intros n m r.
  destruct n as [|n].
  - follow (rule2_step 0 m r).
    replace (desc (S 0) m) with (g (S 0) m) by reflexivity.
    finish_cfg.
  - follow (rule2_step (S n) m r).
    follow (IH n (g (S (S n)) m) r).
    replace (desc (S (S n)) m) with (desc (S n) (g (S (S n)) m)) by reflexivity.
    finish_cfg.
Qed.

(** ** One round of the tail automaton. *)

Definition round (m : nat) : nat := desc (2 * m + 2) (g (2 * m + 2) 0).

Lemma round_step : forall x y r,
  y = round x ->
  Bcfg (2 * x + 3) 1 0 (0 >> r) -->* Bcfg 1 0 y (0 >> r).
Proof.
  intros x y r Hy.
  replace (2 * x + 3) with (S (2 * x + 2)) by lia.
  eapply evstep_trans;
    [apply (B_rule_gen (2 * x + 2) 1 0%nat (0 >> r) (g (2 * x + 2) 0));
     reflexivity |].
  replace (S (2 * x + 2)) with (S (S (2 * x + 1))) by lia.
  follow (rule2_phase (2 * x + 1) (g (2 * x + 2) 0) r).
  replace (S (2 * x + 1)) with (2 * x + 2) by lia.
  replace (desc (2 * x + 2) (g (2 * x + 2) 0)) with (round x) by reflexivity.
  rewrite Hy. finish.
Qed.

(** One 0-marker: [B(1,0,m) 0 0 r -> B(1,0,round m) 0 r]. *)
Lemma tail_zero : forall m r,
  Bcfg 1 0 m (0 >> 0 >> r) -->* Bcfg 1 0 (round m) (0 >> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply rule3a |].
  apply round_step. reflexivity.
Qed.

(** Consume n zeros from a block of n+1 zeros; one marker 0 remains. *)
Lemma tail_zeros : forall n m r,
  Bcfg 1 0 m ([0]^^(S n) *> r) -->*
  Bcfg 1 0 (Nat.iter n round m) (0 >> r).
Proof.
  intros n. induction n as [|n IH]; intros m r.
  - replace ([0]^^(S 0) *> r) with (0 >> r) by reflexivity.
    replace (Nat.iter 0 round m) with m by reflexivity.
    finish.
  - replace ([0]^^(S (S n)) *> r) with (0 >> ([0]^^(S n) *> r)) by reflexivity.
    follow (tail_zero m ([0]^^n *> r)).
    follow (IH (round m) r).
    rewrite iter_succ_r. finish.
Qed.

(** ** The four rounds of the tail automaton. *)

(** From B(2,1,0) reading a leading 0, the initial descent produces m = 6. *)
Lemma initial_desc : forall r,
  Bcfg 2 1 0 (0 >> r) -->* Bcfg 1 0 6 (0 >> r).
Proof.
  intros r.
  eapply evstep_trans; [apply (B_rule 1 1 0%nat (0 >> r)) |].
  replace (Nat.iter 1 (g 1) 0%nat) with 2%nat by (vm_compute; reflexivity).
  eapply evstep_trans; [apply (rule2_phase 0 2%nat r) |].
  replace (desc (S 0) 2%nat) with 6%nat by (vm_compute; reflexivity).
  finish.
Qed.

(** A reset marker 1: [B(1,0,m) 0 1 r -> B(2,1,0) 0^(2m+3) r],
    followed immediately by the initial descent back to level 1. *)
Lemma tail_reset : forall m r,
  Bcfg 1 0 m (0 >> 1 >> r) -->*
  Bcfg 1 0 6 ([0]^^(2 * m + 3) *> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply rule3b |].
  replace (2 * m + 3) with (S (2 * m + 2)) by lia.
  change (Bcfg 2 1 0 (0 >> ([0]^^(2 * m + 2) *> r)) -->*
          Bcfg 1 0 6 (0 >> ([0]^^(2 * m + 2) *> r))).
  apply initial_desc.
Qed.

(** One full epoch: a reset marker [1], the new zero block it creates, and the
    descent through that whole block (all but the last 0).  Keeping [next]
    opaque to conversion is essential: unfolding it would expose [Nat.iter ...
    round ...] and force evaluation of an Ackermann-level number. *)
Definition next (m : nat) : nat := Nat.iter (2 * m + 2) round 6%nat.

Lemma epoch : forall m r,
  Bcfg 1 0 m (0 >> 1 >> r) -->* Bcfg 1 0 (next m) (0 >> r).
Proof.
  intros m r. unfold next.
  eapply evstep_trans; [apply (tail_reset m r) |].
  replace (2 * m + 3) with (S (2 * m + 2)) by lia.
  apply tail_zeros.
Qed.


(** ** The new 2-marker: [B(1,0,m) 0 2 r -> B(1,0,gamma m) 0 r].
    The rule3c reset creates a fresh zero block and a fresh 1 block of length
    2m+3; the former is consumed by two rounds, the latter by 2m+3 epochs. *)

Definition gamma (m : nat) : nat := Nat.iter (2 * m + 3) next (Nat.iter 2 round 6%nat).

Lemma tail_epochs : forall n m r,
  Bcfg 1 0 m (0 >> [1]^^n *> r) -->*
  Bcfg 1 0 (Nat.iter n next m) (0 >> r).
Proof.
  intros n; induction n as [|n IH]; intros m r.
  - replace ([1]^^0 *> r) with r by reflexivity.
    replace (Nat.iter 0 next m) with m by reflexivity. finish.
  - replace ([1]^^(S n) *> r) with (1 >> [1]^^n *> r) by reflexivity.
    eapply evstep_trans; [apply (epoch m ([1]^^n *> r)) |].
    follow (IH (next m) r).
    rewrite iter_succ_r. finish.
Qed.

Lemma tail_mark2 : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->* Bcfg 1 0 (gamma m) (0 >> r).
Proof.
  intros m r. unfold gamma.
  eapply evstep_trans with (c' := (Bcfg 2 1 0 (0 >> 0 >> 0 >> [1]^^(2*m+3) *> r))).
  { apply (rule3c m r). }
  eapply evstep_trans with (c' := (Bcfg 1 0 6%nat (0 >> 0 >> 0 >> [1]^^(2*m+3) *> r))).
  { apply (initial_desc ([0;0] *> [1]^^(2*m+3) *> r)). }
  eapply evstep_trans with (c' := (Bcfg 1 0 (Nat.iter 2 round 6%nat) (0 >> [1]^^(2*m+3) *> r))).
  { change (Bcfg 1 0 6%nat ([0;0;0] *> [1]^^(2*m+3) *> r) -->* (Bcfg 1 0 (Nat.iter 2 round 6%nat) (0 >> [1]^^(2*m+3) *> r))).
    apply (tail_zeros 2 6%nat ([1]^^(2*m+3) *> r)). }
  apply (tail_epochs (2*m+3) (Nat.iter 2 round 6%nat) r).
Qed.

(** ** The parameter chain.  Tail: 0^3, then two 1s, then twenty-one 2s, then 3. *)
Definition m1 : nat := Nat.iter 2 round 6%nat.
Definition m2 : nat := next m1.
Definition m3 : nat := next m2.
Definition m4 : nat := gamma m3.
Definition m5 : nat := gamma m4.
Definition m6 : nat := gamma m5.
Definition m7 : nat := gamma m6.
Definition m8 : nat := gamma m7.
Definition m9 : nat := gamma m8.
Definition m10 : nat := gamma m9.
Definition m11 : nat := gamma m10.
Definition m12 : nat := gamma m11.
Definition m13 : nat := gamma m12.
Definition m14 : nat := gamma m13.
Definition m15 : nat := gamma m14.
Definition m16 : nat := gamma m15.
Definition m17 : nat := gamma m16.
Definition m18 : nat := gamma m17.
Definition m19 : nat := gamma m18.
Definition m20 : nat := gamma m19.
Definition m21 : nat := gamma m20.
Definition m22 : nat := gamma m21.
Definition m23 : nat := gamma m22.
Definition m24 : nat := gamma m23.

Lemma m1_eq : m1 = Nat.iter 2 round 6%nat. Proof. reflexivity. Qed.
Lemma m2_eq : m2 = next m1. Proof. reflexivity. Qed.
Lemma m3_eq : m3 = next m2. Proof. reflexivity. Qed.
Lemma m4_eq : m4 = gamma m3. Proof. reflexivity. Qed.
Lemma m5_eq : m5 = gamma m4. Proof. reflexivity. Qed.
Lemma m6_eq : m6 = gamma m5. Proof. reflexivity. Qed.
Lemma m7_eq : m7 = gamma m6. Proof. reflexivity. Qed.
Lemma m8_eq : m8 = gamma m7. Proof. reflexivity. Qed.
Lemma m9_eq : m9 = gamma m8. Proof. reflexivity. Qed.
Lemma m10_eq : m10 = gamma m9. Proof. reflexivity. Qed.
Lemma m11_eq : m11 = gamma m10. Proof. reflexivity. Qed.
Lemma m12_eq : m12 = gamma m11. Proof. reflexivity. Qed.
Lemma m13_eq : m13 = gamma m12. Proof. reflexivity. Qed.
Lemma m14_eq : m14 = gamma m13. Proof. reflexivity. Qed.
Lemma m15_eq : m15 = gamma m14. Proof. reflexivity. Qed.
Lemma m16_eq : m16 = gamma m15. Proof. reflexivity. Qed.
Lemma m17_eq : m17 = gamma m16. Proof. reflexivity. Qed.
Lemma m18_eq : m18 = gamma m17. Proof. reflexivity. Qed.
Lemma m19_eq : m19 = gamma m18. Proof. reflexivity. Qed.
Lemma m20_eq : m20 = gamma m19. Proof. reflexivity. Qed.
Lemma m21_eq : m21 = gamma m20. Proof. reflexivity. Qed.
Lemma m22_eq : m22 = gamma m21. Proof. reflexivity. Qed.
Lemma m23_eq : m23 = gamma m22. Proof. reflexivity. Qed.
Lemma m24_eq : m24 = gamma m23. Proof. reflexivity. Qed.

Opaque m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 gamma next round.

(** The tail before the halting 3 is twenty-one 2s. *)
Definition tail21 : Stream sym :=
  [S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> (3 >> 2 >> 1 >> const 0).

Lemma reaches_before_halt : c0 -->* Bcfg 1 0 m24 (0 >> 3 >> 2 >> 1 >> const 0).
Proof.
  eapply evstep_trans; [apply start_B |].
  eapply evstep_trans; [apply initial_desc |].
  eapply evstep_trans; [apply (tail_zeros 2 6%nat ([1;1] *> tail21)) |].
  rewrite <- m1_eq.
  eapply evstep_trans; [apply (epoch m1 (1 >> tail21)) |].
  rewrite <- m2_eq.
  eapply evstep_trans; [apply (epoch m2 tail21) |].
  rewrite <- m3_eq.
  unfold tail21.
  eapply evstep_trans; [apply (tail_mark2 m3 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m4_eq.
  eapply evstep_trans; [apply (tail_mark2 m4 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m5_eq.
  eapply evstep_trans; [apply (tail_mark2 m5 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m6_eq.
  eapply evstep_trans; [apply (tail_mark2 m6 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m7_eq.
  eapply evstep_trans; [apply (tail_mark2 m7 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m8_eq.
  eapply evstep_trans; [apply (tail_mark2 m8 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m9_eq.
  eapply evstep_trans; [apply (tail_mark2 m9 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m10_eq.
  eapply evstep_trans; [apply (tail_mark2 m10 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m11_eq.
  eapply evstep_trans; [apply (tail_mark2 m11 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m12_eq.
  eapply evstep_trans; [apply (tail_mark2 m12 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m13_eq.
  eapply evstep_trans; [apply (tail_mark2 m13 ([S2;S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m14_eq.
  eapply evstep_trans; [apply (tail_mark2 m14 ([S2;S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m15_eq.
  eapply evstep_trans; [apply (tail_mark2 m15 ([S2;S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m16_eq.
  eapply evstep_trans; [apply (tail_mark2 m16 ([S2;S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m17_eq.
  eapply evstep_trans; [apply (tail_mark2 m17 ([S2;S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m18_eq.
  eapply evstep_trans; [apply (tail_mark2 m18 ([S2;S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m19_eq.
  eapply evstep_trans; [apply (tail_mark2 m19 ([S2;S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m20_eq.
  eapply evstep_trans; [apply (tail_mark2 m20 ([S2;S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m21_eq.
  eapply evstep_trans; [apply (tail_mark2 m21 ([S2;S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m22_eq.
  eapply evstep_trans; [apply (tail_mark2 m22 ([S2] *> 3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m23_eq.
  eapply evstep_trans; [apply (tail_mark2 m23 (3 >> 2 >> 1 >> const 0)) |].
  rewrite <- m24_eq.
  finish.
Qed.

(** ** Seal the final parameter. *)
Lemma m24_spec : {x : nat | x = m24}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition mfin : nat := proj1_sig m24_spec.
Lemma mfin_eq : mfin = m24.
Proof. exact (proj2_sig m24_spec). Qed.
Opaque mfin.

(** ** The halting configuration: F reads the 3. *)
Definition c_final : Q * tape :=
  (1 >> ([1]^^(S (S (S (2 * mfin)))) *> const 0)) {{F}}> (3 >> 2 >> 1 >> const 0).

Lemma reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply reaches_before_halt |].
  rewrite <- mfin_eq.
  unfold c_final.
  apply (halt_from_B mfin (2 >> 1 >> const 0)).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb74_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Sigma. *)
Definition sigma : nat := 2 * mfin + 7.
Definition final_cells : list sym := [S1]^^(2 * mfin + 4) ++ [S1; S2; S1].

Lemma lpow_length : forall j (ys : list sym), length (ys ^^ j) = j * length ys.
Proof.
  induction j as [|j IH]; intros ys.
  - reflexivity.
  - simpl. rewrite length_app, IH. lia.
Qed.

Lemma in_lpow : forall j (ys : list sym) x, In x (ys ^^ j) -> In x ys.
Proof.
  induction j as [|j IH]; intros ys x H.
  - destruct H.
  - simpl in H. apply in_app_or in H as [H | H].
    + exact H.
    + exact (IH ys x H).
Qed.

Lemma cells_count : forall x : nat,
  length ([S1]^^(2 * x + 4) ++ [S1; S2; S1]) = 2 * x + 7.
Proof.
  intros x.
  rewrite !length_app, (lpow_length (2 * x + 4) [S1]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([S1]^^(2 * x + 4) ++ [S1; S2; S1]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank mfin y H). Qed.
