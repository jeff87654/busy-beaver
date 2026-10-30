(** * The BB(4,4) champion 0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC halts; exact final tape *)

(** Configurations (Ligocki notation, head on the first 1):
      B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R          = [Bcfg k n m r]
    Function (BB44_rules.v):  g_0(m) = m+1,  g_(k+1)(m) = g_k^(2m+2)(0).
    Rules (BB44_rules.v):
      B_rule : B(k, n, m) R -->* B(k, 0, g_(k-1)^n(m)) R          (for k >= 1)
      B_phase: B(2, 0, m) R -->* B(1, 2m+2, 0) R                 (BB(4,4) specific)
      D_phase: B(1, 0, m) R -->* B(2m+2, 1, 0) R 2 1 3           (BB(4,4) specific)
    Run:
      0^inf A> 0^inf  -(98 steps)->  B(2, 6, 0)  0^inf
                                   ->  B(2, 0, 126)  0^inf           (B_rule)
                                   ->  B(1, 254, 0)  0^inf           (B_phase)
                                   ->  B(1, 0, 254)  0^inf           (B_rule)
                                   ->  B(510, 1, 0)  2 1 3 0^inf     (D_phase)
                                   ->  B(510, 0, g_509(0))  2 1 3 0^inf   (B_rule)
                                   -(the halting transition A2 = 1RZ)->  HALT,
    halting with the head (state A) reading the 2, with tape
      0^inf  3^(2 g_509(0) + 1)  2^510  A> 2 1 3 0^inf.
    The halting write turns that 2 into a 1, so the final tape holds exactly
    [2 * g_509(0) + 514] nonzero symbols (see sigma below).

    A note on [g509].  The number [g_509(0)] is astronomically large and the
    term [g 509] is *not* evaluable: [g 509 x] iterates [g 508] [2x+2] times,
    so unfolding it requires unfolding its argument as well -- normalising
    [g 509] costs exponentially many reduction steps.  Two precautions keep
    the development fast:
      - [g509] is sealed behind a [sig], so [simpl] and [lia] treat it as an
        opaque atom and never try to evaluate it;
      - every configuration that mentions the score mentions it through the
        *same* term [g509], so no proof ever has to compare [g509] with the
        raw [Nat.iter 1 (g 509) 0].  Where such a comparison would be needed
        (the B-rule), the result is abstracted away first ([B_rule_gen]). *)

From TM44 Require Import Individual44 BB44_rules BB44_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(510, 1, 0) 2 1 3 0^inf].

    The first 98 steps are proved in [BB44_start.v], which cuts the run into
    chunks of 10 steps (one monolithic [execute] over all 98 steps needs
    O(n^3) rewriting and exhausts coqc's memory).  [start_raw] there is
    [c0 -->* cfg_98] with [cfg_98 = Bcfg 2 6 0 (const 0)].  The rest of the
    start is the two BB(4,4)-specific phases, glued together with Ligocki's
    descent rule [B_rule]. *)
Lemma start : c0 -->* Bcfg 510 1 0 (2 >> (1 >> (3 >> const 0))).
Proof.
  eapply evstep_trans; [apply start_raw |].
  (* phase A: Ligocki's descent with k = 1, n = 6 *)
  eapply evstep_trans; [apply (B_rule 1 6 0 (const 0)) |].
  (* phase B: B(2, 0, 126) -> B(1, 254, 0) *)
  eapply evstep_trans; [apply (B_phase 126) |].
  (* phase C: Ligocki's descent with k = 0, n = 254 *)
  eapply evstep_trans; [apply (B_rule 0 254 0 (const 0)) |].
  (* phase D: B(1, 0, 254) -> B(510, 1, 0) 2 1 3 *)
  apply (D_phase 254).
Qed.

(** ** The score-carrying number [g509 = g_509(0)], sealed. *)
Lemma g509_spec : {x : nat | x = Nat.iter 1 (g 509) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition g509 : nat := proj1_sig g509_spec.
Lemma g509_eq : g509 = Nat.iter 1 (g 509) 0%nat.
Proof. exact (proj2_sig g509_spec). Qed.

(** ** [B_rule] with its result abstracted.

    This is [B_rule] of BB44_rules.v with the (huge) number [Nat.iter n (g k) m]
    replaced by an arbitrary [x].  Instantiating it with [x := g509] lets us
    state the rule with the sealed term, so that no conversion between
    [g509] and the raw term is ever required. *)
Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** The rule at level 509, applied to the configuration reached by the start. *)
Lemma B_rule_509 :
  Bcfg 510 1 0 (2 >> (1 >> (3 >> const 0))) -->*
  Bcfg 510 0 g509 (2 >> (1 >> (3 >> const 0))).
Proof.
  apply (B_rule_gen 509 1 0 (2 >> (1 >> (3 >> const 0))) g509 g509_eq).
Qed.

(** The halting configuration: state A reading the 2, i.e. the configuration on which the
    halting transition A2 = 1RZ applies (busycoq stops there, without performing the write). *)
Definition c_final : Q * tape := Bcfg 510 0 g509 (2 >> (1 >> (3 >> const 0))).

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start |].
  apply B_rule_509.
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb44_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Sigma: the number of nonzero cells on the tape after the halting write.
    The halting transition A2 = 1RZ writes a 1 over the 2 it reads, so the final tape is
      0^inf  3^(2 g509 + 1)  2^510  1  1  3  0^inf
    which has (2 g509 + 1) + 510 + 3 = 2 g509 + 514 nonzero cells. *)
Definition sigma : nat := 2 * g509 + 514.

(** The nonzero cells of the final tape, listed from left to right. *)
Definition final_cells : list sym := [3]^^(2 * g509 + 1) ++ [2]^^510 ++ [S1;S1;S3].

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
    instantiated with [g509] afterwards.  That way no tactic ever has to look
    at [g509], which is opaque anyway. *)

Lemma cells_count : forall x : nat,
  length ([3]^^(2 * x + 1) ++ [2]^^510 ++ [S1;S1;S3]) = 2 * x + 514.
Proof.
  intros x.
  rewrite !app_length, (lpow_length (2 * x + 1) [3]), (lpow_length 510 [2]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([3]^^(2 * x + 1) ++ [2]^^510 ++ [S1;S1;S3]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall x, In x final_cells -> x <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank g509 y H). Qed.
