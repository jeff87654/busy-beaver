(** * Complete halting trajectory and exact final tape of the BB(6,4) machine
      1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ

    This machine is the 54-L BB(5,4) champion with the halting transition
    B1 = 1RZ replaced by B1 = 1RF and an extra state F.  Hence every macro
    step of 54-L up to its halting configuration applies verbatim here; only
    the last transition is replaced by four further rounds:

      B(5,1,0) -> B(5,0,M1) -> B_sweep(0^inf) -> B(1,0,1) 2^(2M1+5) 011
        -> D_chain -> B(k1,0,m1) 011
        -> sweep(011->031) + D_chain -> B(k2,0,m2) 031
        -> sweep(031->001) + D_chain -> B(k3,0,m3) 001
        -> sweep(001->0131) + D_chain -> B(k4,0,m4) 0131
        -> final_halt (F3 = 1RZ).

    Every round raises the Knuth-arrow level of the descending parameter;
    four rounds lift the score above f_{omega+1}^4(65536). *)

From TM64 Require Import Individual64 BB64_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sealed constants.  Never unfolded during reduction. *)

Lemma M1_spec : {x : nat | x = Nat.iter 1 (g 4) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M1 : nat := proj1_sig M1_spec.
Lemma M1_eq : M1 = Nat.iter 1 (g 4) 0%nat.
Proof. exact (proj2_sig M1_spec). Qed.

(** The result of a D_chain from (k,m), sealed as a pair. *)
Definition seal_pair (c k m : nat) : nat * nat := Nat.iter c step_pair (k, m).

(** The successive (K,M) pairs after each D_chain. *)
Definition P1 : nat * nat := Nat.iter (2 * M1 + 5) step_pair (0%nat, 1%nat).
Definition k1 : nat := S (fst P1).
Definition m1 : nat := snd P1.

Definition P2 : nat * nat := Nat.iter (k1 + 2 * m1) step_pair (0%nat, 1%nat).
Definition k2 : nat := S (fst P2).
Definition m2 : nat := snd P2.

Definition P3 : nat * nat := Nat.iter (k2 + 2 * m2) step_pair (0%nat, 1%nat).
Definition k3 : nat := S (fst P3).
Definition m3 : nat := snd P3.

Definition P4 : nat * nat := Nat.iter (k3 + 2 * m3) step_pair (0%nat, 1%nat).
Definition k4 : nat := S (fst P4).
Definition m4 : nat := snd P4.

(** ** Abstracted wrappers (sealed constants never trigger reduction). *)

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

Theorem D_chain_gen : forall c k m r K M,
  (K, M) = Nat.iter c step_pair (k, m) ->
  Bcfg (S k) 0 m ([2]^^c *> r) -->* Bcfg (S K) 0 M r.
Proof.
  intros c k m r K M H.
  assert (HK : K = fst (Nat.iter c step_pair (k, m))) by (rewrite <- H; reflexivity).
  assert (HM : M = snd (Nat.iter c step_pair (k, m))) by (rewrite <- H; reflexivity).
  subst K M. apply D_chain.
Qed.

(** ** The first phase, identical to 54-L. *)

Lemma M1_reservoir : 2 * M1 + 5 = 2 * M1 + 5. Proof. reflexivity. Qed.

(** start -> B(5,1,0), 25 steps (from BB64_rules.v). *)
Lemma start : c0 -->* Bcfg 5 1 0 (Streams.const S0).
Proof. apply start_to_B5. Qed.

(** B(5,1,0) -> B(5,0,M1). *)
Lemma descent1 : Bcfg 5 1 0 (Streams.const S0) -->* Bcfg 5 0 M1 (Streams.const S0).
Proof. apply (B_rule_gen 4 1 0 (Streams.const S0) M1 M1_eq). Qed.

(** B(5,0,M1) 0^inf -> B(1,0,1) 2^(2M1+5) 011. *)
Lemma sweep1 : Bcfg 5 0 M1 (Streams.const S0) -->*
  Bcfg 1 0 1 ([2]^^(2 * M1 + 5) *> (S0 >> S1 >> S1 >> Streams.const S0)).
Proof.
  change (Bcfg 5 0 M1 (const 0) -->*
    Bcfg 1 0 1 ([2]^^(2 * M1 + 5) *> (0 >> 1 >> 1 >> const 0))).
  apply B_sweep.
Qed.

(** D_chain: B(1,0,1) 2^(2M1+5) 011 -> B(k1,0,m1) 011. *)
Lemma dchain1 : Bcfg 1 0 1 ([2]^^(2 * M1 + 5) *> (S0 >> S1 >> S1 >> Streams.const S0)) -->*
  Bcfg k1 0 m1 (S0 >> S1 >> S1 >> Streams.const S0).
Proof.
  unfold k1, m1, P1.
  apply (D_chain_gen (2 * M1 + 5) 0%nat 1%nat
    (0 >> 1 >> 1 >> const 0) (fst (Nat.iter (2 * M1 + 5) step_pair (0%nat, 1%nat)))
    (snd (Nat.iter (2 * M1 + 5) step_pair (0%nat, 1%nat)))).
  symmetry; apply surjective_pairing.
Qed.

(** ** The four new rounds. *)

(** Round 2: B(k1,0,m1) 011 -> B(1,0,1) 2^(k1+2m1) 031 -> B(k2,0,m2) 031. *)
Lemma round2 : Bcfg k1 0 m1 (S0 >> S1 >> S1 >> Streams.const S0) -->*
  Bcfg k2 0 m2 (S0 >> S3 >> S1 >> Streams.const S0).
Proof.
  change (Bcfg k1 0 m1 (0 >> 1 >> 1 >> const 0) -->*
    Bcfg k2 0 m2 (0 >> 3 >> 1 >> const 0)).
  eapply evstep_trans.
  - apply B_sweep_011_031.
  - unfold k2, m2, P2.
    apply (D_chain_gen (k1 + 2 * m1) 0%nat 1%nat
      (0 >> 3 >> 1 >> const 0)
      (fst (Nat.iter (k1 + 2 * m1) step_pair (0%nat, 1%nat)))
      (snd (Nat.iter (k1 + 2 * m1) step_pair (0%nat, 1%nat)))).
    symmetry; apply surjective_pairing.
Qed.

(** Round 3: 031 -> 001. *)
Lemma round3 : Bcfg k2 0 m2 (S0 >> S3 >> S1 >> Streams.const S0) -->*
  Bcfg k3 0 m3 (S0 >> S0 >> S1 >> Streams.const S0).
Proof.
  change (Bcfg k2 0 m2 (0 >> 3 >> 1 >> const 0) -->*
    Bcfg k3 0 m3 (0 >> 0 >> 1 >> const 0)).
  eapply evstep_trans.
  - apply B_sweep_031_001.
  - unfold k3, m3, P3.
    apply (D_chain_gen (k2 + 2 * m2) 0%nat 1%nat
      (0 >> 0 >> 1 >> const 0)
      (fst (Nat.iter (k2 + 2 * m2) step_pair (0%nat, 1%nat)))
      (snd (Nat.iter (k2 + 2 * m2) step_pair (0%nat, 1%nat)))).
    symmetry; apply surjective_pairing.
Qed.

(** Round 4: 001 -> 0131. *)
Lemma round4 : Bcfg k3 0 m3 (S0 >> S0 >> S1 >> Streams.const S0) -->*
  Bcfg k4 0 m4 (S0 >> S1 >> S3 >> S1 >> Streams.const S0).
Proof.
  change (Bcfg k3 0 m3 (0 >> 0 >> 1 >> const 0) -->*
    Bcfg k4 0 m4 (0 >> 1 >> 3 >> 1 >> const 0)).
  eapply evstep_trans.
  - apply B_sweep_001_0131.
  - unfold k4, m4, P4.
    apply (D_chain_gen (k3 + 2 * m3) 0%nat 1%nat
      (0 >> 1 >> 3 >> 1 >> const 0)
      (fst (Nat.iter (k3 + 2 * m3) step_pair (0%nat, 1%nat)))
      (snd (Nat.iter (k3 + 2 * m3) step_pair (0%nat, 1%nat)))).
    symmetry; apply surjective_pairing.
Qed.

(** The halting configuration. *)
Definition c_final : Q * tape :=
  (S1 >> (S1 >> ([2]^^k4 *> ([3]^^(2 * m4 + 1) *> const 0))) {{F}}> (S3 >> S1 >> Streams.const S0)).

Lemma reaches_final_halt : Bcfg k4 0 m4 (S0 >> S1 >> S3 >> S1 >> Streams.const S0) -->* c_final.
Proof.
  unfold c_final.
  unfold k4.
  change (Bcfg (S (fst P4)) 0 m4 (0 >> 1 >> 3 >> 1 >> const 0) -->*
    (1 >> (1 >> ([2]^^(S (fst P4)) *> ([3]^^(2 * m4 + 1) *> const 0))) {{F}}> (3 >> 1 >> const 0))).
  apply final_halt.
Qed.

(** The whole run. *)
Theorem reaches_c_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start |].
  eapply evstep_trans; [apply descent1 |].
  eapply evstep_trans; [apply sweep1 |].
  eapply evstep_trans; [apply dchain1 |].
  eapply evstep_trans; [apply round2 |].
  eapply evstep_trans; [apply round3 |].
  eapply evstep_trans; [apply round4 |].
  apply reaches_final_halt.
Qed.

Theorem c_final_halted : halted tm c_final.
Proof. unfold c_final, tm. reflexivity. Qed.

Theorem bb64_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_c_final | apply c_final_halted]. Qed.
