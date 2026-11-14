(** * Halting run and final tape of Argon's BB(4,4) machine 44-A
      1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD

    c0 -->* Bcfg 5 4 0 0^inf                                   (91 literal steps)
       -->* Bcfg 5 0 M1 0^inf                                  (B_rule, M1 = g_4^4(0))
       -->* Bcfg (2M1+1) 3 0 [3^3 1] 0^inf                     (lift)
       -->* Bcfg (2M1+1) 0 M2 [3^3 1] 0^inf                    (B_rule, M2 = g_(2M1)^3(0))
       -->* Bcfg (2M1+1) (2M2+3) 0 [3 1] 0^inf                 (lift2)
       -->* Bcfg (2M1+1) 0 M3 [3 1] 0^inf                      (B_rule, M3 = g_(2M1)^(2M2+3)(0))
       -->  c_final = 0^inf 2^(2M3+1) 3^(2M1+1) 0 B> 1 0^inf    (A3 = 0RB; B1 = 1RZ halts)
    The halting transition B1 = 1RZ writes 1 over the scanned 1, so the final tape has
    sigma = (2M3+1) + (2M1+1) + 1 = 2 M3 + 2 M1 + 3 nonzero cells (nonzero_cells, proved). *)

From Local Require Import Individual44 BB44A_rules.
From Local Require BB44_rules.
From Coq Require Import Lia PeanoNat List Streams.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sealed constants *)

Lemma M1_spec : {x : nat | x = Nat.iter 4 (g 4) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M1 : nat := proj1_sig M1_spec.
Lemma M1_eq : M1 = Nat.iter 4 (g 4) 0%nat.
Proof. exact (proj2_sig M1_spec). Qed.

Lemma M2_spec : {x : nat | x = Nat.iter 3 (g (2 * M1)) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2 : nat := proj1_sig M2_spec.
Lemma M2_eq : M2 = Nat.iter 3 (g (2 * M1)) 0%nat.
Proof. exact (proj2_sig M2_spec). Qed.

Lemma M3_spec : {x : nat | x = Nat.iter (2 * M2 + 3) (g (2 * M1)) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M3 : nat := proj1_sig M3_spec.
Lemma M3_eq : M3 = Nat.iter (2 * M2 + 3) (g (2 * M1)) 0%nat.
Proof. exact (proj2_sig M3_spec). Qed.

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

Definition c_final : Q * tape := c_halt (S (2 * M1)) M3.

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start_to_B5|].
  eapply evstep_trans; [apply (B_rule_gen 4 4 0 (const 0) M1 M1_eq)|].
  eapply evstep_trans; [apply (lift 3 M1)|].
  eapply evstep_trans; [apply (B_rule_gen (2 * M1) 3 0 ([3]^^3 *> 1 >> const 0) M2 M2_eq)|].
  eapply evstep_trans; [apply (lift2 (2 * M1) 1 M2 (1 >> const 0))|].
  eapply evstep_trans; [apply (B_rule_gen (2 * M1) (2 * M2 + 3) 0 ([3]^^1 *> 1 >> const 0) M3 M3_eq)|].
  apply to_halt.
Qed.

Theorem final_halted : halted tm c_final.
Proof. apply c_halt_halted. Qed.

Theorem bb44A_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** The score *)

Definition sigma : nat := 2 * M3 + 2 * M1 + 3.

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
  exists B, ([S0] ++ [S3]^^(S (2 * M1)) ++ [S2]^^(2 * M3 + 1)), (@nil sym), S1.
  split.
  - unfold c_final, c_halt. rewrite !Str_app_assoc. reflexivity.
  - unfold sigma. rewrite !cnt_app, !cnt_lpow. cbn [cnt nzv]. lia.
Qed.

Theorem c_final_head : exists l r, c_final = (B, (l, S1, r)) /\ tm (B, S1) = None.
Proof.
  exists (S0 >> [S3]^^(S (2 * M1)) *> [S2]^^(2 * M3 + 1) *> const S0), (const S0).
  split; reflexivity.
Qed.

Print Assumptions reaches_final.
Print Assumptions bb44A_halts.
Print Assumptions c_final_nonzero.
