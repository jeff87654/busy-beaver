(** * The BB(3,4) champion 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC halts; exact final tape *)

(** Configurations (Ligocki notation, head on the first 1):
      B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R          = [Bcfg k n m r]
    Function (BB34_rules.v):  g_0(m) = m+1,  g_(k+1)(m) = g_k^(2m+2)(0).
    Rules (BB34_rules.v):
      B_rule : B(k, n, m) R -->* B(k, 0, g_(k-1)^n(m)) R          (for k >= 1)
    Run (Ligocki, 2024-05-22):
      0^inf A> 0^inf  -(241 steps)->  B(16, 3, 0)  2  0^inf
                                   ->  B(16, 0, g_15^3(0))  2  0^inf
                                   -(the halting transition A2 = 1RZ)->  HALT,
    halting with the head (state A) reading the 2, with tape
      0^inf  3^(2 g_15^3(0) + 1)  2^16  A> 2  0^inf.
    The halting write turns that 2 into a 1, so the final tape holds exactly
    [2 * g_15^3(0) + 18] nonzero symbols (see sigma below).

    A note on [g15].  The number [g_15^3(0)] is astronomically large and the
    term [g 15] is *not* evaluable: [g 15 x] iterates [g 14] [2x+2] times,
    so unfolding it requires unfolding its argument as well -- normalising
    [g 15] costs exponentially many reduction steps.  Two precautions keep
    the development fast:
      - [g15] is sealed behind a [sig], so [simpl] and [lia] treat it as an
        opaque atom and never try to evaluate it;
      - every configuration that mentions the score mentions it through the
        *same* term [g15], so no proof ever has to compare [g15] with the
        raw [Nat.iter 3 (g 15) 0].  Where such a comparison would be needed
        (the B-rule), the result is abstracted away first ([B_rule_gen]). *)

From TM34 Require Import Individual34 BB34_rules BB34_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(16, 3, 0) 2 0^inf] in 241 steps.

    The 241 steps are proved in [BB34_start.v], which cuts the run into
    chunks of 10 steps (one monolithic [execute] over all 241 steps needs
    O(n^3) rewriting and exhausts coqc's memory).  [start_raw] there is
    [c0 -->* cfg_241]. *)
Lemma start : c0 -->* Bcfg 16 3 0 (2 >> const 0).
Proof.
  rewrite <- cfg_241_is_B.
  apply start_raw.
Qed.

(** ** The score-carrying number [g15 = g_15^3(0)], sealed. *)
Lemma g15_spec : {x : nat | x = Nat.iter 3 (g 15) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition g15 : nat := proj1_sig g15_spec.
Lemma g15_eq : g15 = Nat.iter 3 (g 15) 0%nat.
Proof. exact (proj2_sig g15_spec). Qed.

(** ** [B_rule] with its result abstracted.

    This is [B_rule] of BB34_rules.v with the (huge) number [Nat.iter n (g k) m]
    replaced by an arbitrary [x].  Instantiating it with [x := g15] lets us
    state the rule with the sealed term, so that no conversion between
    [g15] and the raw term is ever required. *)
Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** The rule at level 15, applied to the configuration reached by the start. *)
Lemma B_rule_15 : Bcfg 16 3 0 (2 >> const 0) -->* Bcfg 16 0 g15 (2 >> const 0).
Proof. apply (B_rule_gen 15 3 0 (2 >> const 0) g15 g15_eq). Qed.

(** The halting configuration: state A reading the 2, i.e. the configuration on which the
    halting transition A2 = 1RZ applies (busycoq stops there, without performing the write). *)
Definition c_final : Q * tape := Bcfg 16 0 g15 (2 >> const 0).

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start |].
  apply B_rule_15.
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb34_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Sigma: the number of nonzero cells on the tape after the halting write.
    The halting transition A2 = 1RZ writes a 1 over the 2 it reads, so the final tape is
      0^inf  3^(2 g15 + 1)  2^16  1  Z>  0^inf
    which has (2 g15 + 1) + 16 + 1 = 2 g15 + 18 nonzero cells. *)
Definition sigma : nat := 2 * g15 + 18.

(** The nonzero cells of the final tape, listed from left to right. *)
Definition final_cells : list sym := [3]^^(2 * g15 + 1) ++ [2]^^16 ++ [1].

Lemma lpow_length : forall j (ys : list sym), length (ys ^^ j) = j * length ys.
Proof.
  induction j as [|j IH]; intros ys.
  - reflexivity.
  - simpl. rewrite app_length, IH. lia.
Qed.

Lemma in_lpow : forall j (ys : list sym) x, In x (ys ^^ j) -> In x ys.
Proof.
  induction j as [|j IH]; intros ys x H.
  - destruct H.
  - simpl in H. apply in_app_or in H as [H | H].
    + exact H.
    + exact (IH ys x H).
Qed.

(** The two counting lemmas below are stated for an abstract [x] and only
    instantiated with [g15] afterwards.  That way no tactic ever has to look
    at [g15], which is opaque anyway. *)

Lemma cells_count : forall x : nat,
  length ([3]^^(2 * x + 1) ++ [2]^^16 ++ [1]) = 2 * x + 18.
Proof.
  intros x.
  rewrite !app_length, (lpow_length (2 * x + 1) [3]), (lpow_length 16 [2]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([3]^^(2 * x + 1) ++ [2]^^16 ++ [1]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall x, In x final_cells -> x <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank g15 y H). Qed.
