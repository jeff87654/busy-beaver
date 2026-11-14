(** * Halting run and final tape of Argon's BB(4,4) machine 44-B
      1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD

    c0 -->* Bcfg 2 1 0 [2 1 2 1 2 1 2 1]                      (77 literal steps)
    ladder: Bcfg (k+1) 1 a_k R -B_rule-> Bcfg (k+1) 0 a_(k+1) R -step_up (A2)-> Bcfg (k+2) 1 a_(k+1) R', k = 1..5,
            a_1 = 0, a_(k+1) = g_k(a_k), ending in Bcfg 6 0 a6 0^inf
    phase1 -> Bcfg 4 (2a6+2) 0 [0 3 2 1]   -B_rule-> Bcfg 4 0 b [0 3 2 1],          b = g_3^(2a6+2)(0)
    phase2 -> Bcfg 2 (2b+2) 0 [0 2 1 2 1]  -B_rule-> Bcfg 2 0 c [0 2 1 2 1],        c = g_1^(2b+2)(0)
    phase3 -> Bcfg (2c+3) 1 0 [3 2 1 2 1]  -B_rule-> c_final = Bcfg (2c+3) 0 d [3 2 1 2 1],  d = g_(2c+2)(0)
    c_final: A reads 3, A3 = 1RZ (undefined in Coq): halted.  The 1RZ write turns the 3 into a 1, so
    sigma = (2c+3) + (2d+1) + 1 + 4 = 2c + 2d + 9 nonzero cells (nonzero_cells, proved). *)

From Local Require Import Individual44 BB44B_rules.
From Local Require BB44_rules.
From Coq Require Import Lia PeanoNat List Streams.
Import ListNotations.
Set Default Goal Selector "!".

Lemma a2_spec : {x : nat | x = Nat.iter 1 (g 1) 0%nat}. Proof. exact (exist _ _ eq_refl). Qed.
Definition a2 : nat := proj1_sig a2_spec.
Lemma a2_eq : a2 = Nat.iter 1 (g 1) 0%nat. Proof. exact (proj2_sig a2_spec). Qed.
Lemma a3_spec : {x : nat | x = Nat.iter 1 (g 2) a2}. Proof. exact (exist _ _ eq_refl). Qed.
Definition a3 : nat := proj1_sig a3_spec.
Lemma a3_eq : a3 = Nat.iter 1 (g 2) a2. Proof. exact (proj2_sig a3_spec). Qed.
Lemma a4_spec : {x : nat | x = Nat.iter 1 (g 3) a3}. Proof. exact (exist _ _ eq_refl). Qed.
Definition a4 : nat := proj1_sig a4_spec.
Lemma a4_eq : a4 = Nat.iter 1 (g 3) a3. Proof. exact (proj2_sig a4_spec). Qed.
Lemma a5_spec : {x : nat | x = Nat.iter 1 (g 4) a4}. Proof. exact (exist _ _ eq_refl). Qed.
Definition a5 : nat := proj1_sig a5_spec.
Lemma a5_eq : a5 = Nat.iter 1 (g 4) a4. Proof. exact (proj2_sig a5_spec). Qed.
Lemma a6_spec : {x : nat | x = Nat.iter 1 (g 5) a5}. Proof. exact (exist _ _ eq_refl). Qed.
Definition a6 : nat := proj1_sig a6_spec.
Lemma a6_eq : a6 = Nat.iter 1 (g 5) a5. Proof. exact (proj2_sig a6_spec). Qed.
Lemma b_spec : {x : nat | x = Nat.iter (2 * a6 + 2) (g 3) 0%nat}. Proof. exact (exist _ _ eq_refl). Qed.
Definition bB : nat := proj1_sig b_spec.
Lemma b_eq : bB = Nat.iter (2 * a6 + 2) (g 3) 0%nat. Proof. exact (proj2_sig b_spec). Qed.
Lemma c_spec : {x : nat | x = Nat.iter (2 * bB + 2) (g 1) 0%nat}. Proof. exact (exist _ _ eq_refl). Qed.
Definition cB : nat := proj1_sig c_spec.
Lemma c_eq : cB = Nat.iter (2 * bB + 2) (g 1) 0%nat. Proof. exact (proj2_sig c_spec). Qed.
Lemma d_spec : {x : nat | x = Nat.iter 1 (g (S (2 * cB + 1))) 0%nat}. Proof. exact (exist _ _ eq_refl). Qed.
Definition dB : nat := proj1_sig d_spec.
Lemma d_eq : dB = Nat.iter 1 (g (S (2 * cB + 1))) 0%nat. Proof. exact (proj2_sig d_spec). Qed.

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

Definition c_final : Q * tape := Bcfg (S (S (2 * cB + 1))) 0 dB (3 >> 2 >> 1 >> 2 >> 1 >> const 0).

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start_to_B2|].
  eapply evstep_trans; [apply (B_rule_gen 1 1 0 _ a2 a2_eq)|].
  eapply evstep_trans; [apply step_up|].
  eapply evstep_trans; [apply (B_rule_gen 2 1 a2 _ a3 a3_eq)|].
  eapply evstep_trans; [apply step_up|].
  eapply evstep_trans; [apply (B_rule_gen 3 1 a3 _ a4 a4_eq)|].
  eapply evstep_trans; [apply step_up|].
  eapply evstep_trans; [apply (B_rule_gen 4 1 a4 _ a5 a5_eq)|].
  eapply evstep_trans; [apply step_up|].
  eapply evstep_trans; [apply (B_rule_gen 5 1 a5 _ a6 a6_eq)|].
  eapply evstep_trans; [apply (phase1 3 a6)|].
  eapply evstep_trans; [apply (B_rule_gen 3 (2 * a6 + 2) 0 _ bB b_eq)|].
  eapply evstep_trans; [apply (phase2 1 bB (2 >> 1 >> const 0))|].
  eapply evstep_trans; [apply (B_rule_gen 1 (2 * bB + 2) 0 _ cB c_eq)|].
  eapply evstep_trans; [apply (phase3 cB (2 >> 1 >> const 0))|].
  apply (B_rule_gen (S (2 * cB + 1)) 1 0 _ dB d_eq).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb44B_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** The score *)

Definition sigma : nat := 2 * cB + 2 * dB + 9.

Definition nzv (s : sym) : nat := match s with S0 => 0 | _ => 1 end.

Fixpoint cnt (xs : list sym) : nat :=
  match xs with [] => 0 | x :: t => nzv x + cnt t end.

Definition nonzero_cells (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list sym) (s : sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = cnt L + nzv s + cnt R.

Lemma cnt_app : forall xs ys, cnt (xs ++ ys) = cnt xs + cnt ys.
Proof. induction xs as [|x xs IH]; intros ys; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma cnt_lpow : forall (xs : list sym) n, cnt (xs ^^ n) = n * cnt xs.
Proof. intros xs n. induction n as [|n IH]; simpl; [reflexivity | rewrite cnt_app, IH; lia]. Qed.

Theorem c_final_nonzero : nonzero_cells c_final sigma.
Proof.
  exists A, ([S3]^^(S (S (2 * cB + 1))) ++ [S2]^^(2 * dB + 1)), [S2; S1; S2; S1], S3.
  split.
  - unfold c_final, Bcfg. rewrite !Str_app_assoc. reflexivity.
  - unfold sigma. rewrite !cnt_app, !cnt_lpow. cbn [cnt nzv]. lia.
Qed.

Theorem c_final_head : exists l r, c_final = (A, (l, S3, r)) /\ tm (A, S3) = None.
Proof.
  exists ([S3]^^(S (S (2 * cB + 1))) *> [S2]^^(2 * dB + 1) *> const S0), (S2 >> S1 >> S2 >> S1 >> const S0).
  split; reflexivity.
Qed.

Print Assumptions reaches_final.
Print Assumptions bb44B_halts.
Print Assumptions c_final_nonzero.
