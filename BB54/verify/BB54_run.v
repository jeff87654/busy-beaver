(** * The BB(5,4) champion 1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ
    reaches the Ligocki configuration B(5,1,0) [3 1] 0^inf, and the score
    machinery for its sigma value.

    This machine is the BB(5,4) champion listed on the wiki's Champions
    page (../tools/explore.py checks its equivalence, under the renaming of
    the states A <-> B and of the symbols 2 <-> 3, with the string
    1LD2RA3RB1LC_1LD2LA3RB---_2RA1LA3RC2LC_2RA---2LD2LE_------1RZ1LD).  Its
    runtime is claimed to be larger than [f_w^2 (10 ↑^4 10 ↑↑ 65533)] on the
    wiki's Champions page.

    Configurations (Ligocki notation, head on the first 1):
      B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R          = [Bcfg k n m r]
    Function (BB54_rules.v):  g_0(m) = m+1,  g_(k+1)(m) = g_k^(2m+2)(0).
    Rules (BB54_rules.v):
      B_rule  : B(k, n, m) R -->* B(k, 0, g_(k-1)^n(m)) R          (for k >= 1)
      D_phase : B(2, 0, m) [] -->* B(2m+1, 1, 0) [3 1] 0^inf     (BB(5,4)-specific)
      D_halt  : B(k, 0, m) [] halts for odd k (E3 = 1RZ) and for k = 1.
    Run:
      0^inf A> 0^inf  -(9 steps)->  B(2, 1, 0) 0^inf
                              -(the B rule, level 1)->  B(2, 0, g_1(0)) 0^inf
                                                           = B(2, 0, 2) 0^inf
                              -(the D phase, 14 steps)->  B(5, 1, 0) [3 1] 0^inf
                              -(the B rule, level 4)->  B(5, 0, g_4(0)) [3 1] 0^inf
    The last configuration holds a block of [2 g_4(0) + 1] threes, so the
    tape already carries [2 g_4(0) + 8] nonzero symbols at that point; see
    BB54_score.v for the closed form [2 ↑^3 4 + 4].

    A note on the score-carrying number [g40 = g_4(0)].  The number is
    astronomically large and the term [g 4] is *not* evaluable: [g 4 x]
    iterates [g 3] [2x+2] times, so unfolding it requires unfolding its
    argument as well.  [g40] is therefore sealed behind a [sig], so that
    [simpl] and [lia] treat it as an opaque atom and never try to evaluate
    it; every configuration that mentions the score mentions it through the
    *same* term [g40]. *)

From TM54 Require Import Individual54 BB54_rules BB54_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(2, 1, 0) 0^inf] in 9 steps.

    The 9 steps are proved in [BB54_start.v], which cuts the run into chunks
    of 5 steps. *)
Lemma start : c0 -->* Bcfg 2 1 0 (Streams.const S0).
Proof. apply start_raw. Qed.

(** ** [B_rule] with its result abstracted.

    This is [B_rule] of BB54_rules.v with the (huge) number
    [Nat.iter n (g k) m] replaced by an arbitrary [x].  Instantiating it
    with [x := g40] lets us state the rule with the sealed term, so that no
    conversion between [g40] and the raw term is ever required. *)
Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** ** The score-carrying number [g40 = g_4(0)], sealed. *)
Lemma g40_spec : {x : nat | x = Nat.iter 1%nat (g 4%nat) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition g40 : nat := proj1_sig g40_spec.
Lemma g40_eq : g40 = Nat.iter 1%nat (g 4%nat) 0%nat.
Proof. exact (proj2_sig g40_spec). Qed.

(** ** The first descent: [B(2, 1, 0)] becomes [B(2, 0, g_1(0))] = [B(2, 0, 2)].

    This is the configuration at which the BB(5,4)-specific D/E phase starts:
    two twos and a block of five threes, with the machine in state A on a
    blank cell. *)
Lemma g1_0 : Nat.iter 1%nat (g 1%nat) 0%nat = 2%nat.
Proof.
  change (Nat.iter 2%nat (g 0%nat) 0%nat = 2%nat).
  rewrite (iter_g0 2%nat 0%nat). reflexivity.
Qed.

Lemma descent_1 : Bcfg 2 1 0 (Streams.const S0) -->* Bcfg 2 0 2 (Streams.const S0).
Proof.
  apply (B_rule_gen 1 1 0 (Streams.const S0) 2 g1_0).
Qed.

(** ** The D/E phase: [B(2, 0, 2)] becomes [B(5, 1, 0) [3 1] 0^inf].

    Fourteen steps: the machine eats the two twos (states D and E), walks
    left over the block of five threes (state D), writes a three on the
    blank in front of the block, and sweeps right over the block, turning
    the threes into twos. *)
Lemma D_phase_run : Bcfg 2 0 2 (Streams.const S0) -->* Bcfg 5 1 0 (S3 >> S1 >> Streams.const S0).
Proof. apply D_phase_2. Qed.

(** ** The configuration after the first two descents and the D/E phase. *)
Definition c_score : Q * tape := Bcfg 5 0 g40 (S3 >> S1 >> Streams.const S0).

(** The second descent: [B(5, 1, 0)] becomes [B(5, 0, g_4(0))]. *)
Lemma descent_4 : Bcfg 5 1 0 (S3 >> S1 >> Streams.const S0) -->* c_score.
Proof.
  unfold c_score.
  apply (B_rule_gen 4%nat 1%nat 0%nat (S3 >> S1 >> Streams.const S0) g40 g40_eq).
Qed.

(** ** The whole run, up to the configuration that carries the score. *)
Theorem reaches_score : c0 -->* c_score.
Proof.
  eapply evstep_trans; [apply start |].
  eapply evstep_trans; [apply descent_1 |].
  eapply evstep_trans; [apply D_phase_run |].
  apply descent_4.
Qed.

(** ** Sigma: the number of nonzero cells on the tape of [c_score].

    The tape of [c_score] is
      0^inf  3^(2 g40 + 1)  2^5  A>  3 1  0^inf ,
    so it carries (2 g40 + 1) + 5 + 2 = 2 g40 + 8 nonzero symbols. *)
Definition sigma : nat := 2 * g40 + 8.

(** The nonzero cells of the tape of [c_score], listed from left to right. *)
Definition score_cells : list sym := [S3]^^(2 * g40 + 1) ++ [S2]^^5 ++ [S3; S1].

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
    instantiated with [g40] afterwards.  That way no tactic ever has to look
    at [g40], which is opaque anyway. *)

Lemma cells_count : forall x : nat,
  length ([S3]^^(2 * x + 1) ++ [S2]^^5 ++ [S3; S1]) = 2 * x + 8.
Proof.
  intros x.
  rewrite !app_length, (lpow_length (2 * x + 1) [S3]), (lpow_length 5 [S2]).
  cbn [length]. rewrite !Nat.mul_1_r. lia.
Qed.

Lemma score_cells_count : length score_cells = sigma.
Proof. unfold score_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([S3]^^(2 * x + 1) ++ [S2]^^5 ++ [S3; S1]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Lemma score_cells_all_nonblank : forall x, In x score_cells -> x <> S0.
Proof. intros y H. unfold score_cells in H. exact (cells_nonblank g40 y H). Qed.

(** The number of nonzero cells is at least the length of [score_cells]: the
    tape of [c_score] contains exactly these cells and nothing else. *)
Theorem score_at_least : sigma = length score_cells.
Proof. symmetry. exact score_cells_count. Qed.
