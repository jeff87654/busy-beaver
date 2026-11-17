(** * The BB(3,5) champion 1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC halts *)

(** Configurations (Ligocki notation, head on the first 1):
      B(k, n, m) R  =  0^inf  3^(2m+1)  2^k  A>  1^n  R          = [Bcfg k n m r]
    Function (BB35_rules.v):  g_0(m) = m+1,  g_(k+1)(m) = g_k^(2m+2)(0).
    Rules (BB35_rules.v):
      B_rule : B(k, n, m) R -->* B(k, 0, g_(k-1)^n(m)) R          (for k >= 1)
      rule1  : B(k, 0, m) 2 -->* B(k+2m+1, 0, 0) 4
      rule2  : B(k, 0, m) 4 -->* B(k-1, 2m+2, 0) 4                (for k >= 2)
      rule3  : B(1, 0, m) 4 -->* 3^(2m+3) B> 4                   (and then it halts)
    Run:
      0^inf A> 0^inf  -(241 steps)->  B(16, 3, 0)  2  0^inf
                                   ->  B(16, 0, g_15^3(0))  2  0^inf
                                   -(rule1)->  B(K+13, 0, 0)  4  0^inf
                                   -(rule2, K+12 times)->  B(1, 0, mfin  4  0^inf
                                   -(rule3)->  0^inf 3^(2 mfin + 3)  B> 4  0^inf  (halt),
    where [K = 2 g_15^3(0) + 4 = 2 ↑^15 5] and
    [mfin = desc (K+12) 0] is the value of the "m" parameter after the rule-2
    phase (see [desc] below).

    The BB(3,5) champion agrees with the BB(3,4) champion on the symbols 0..3,
    so the whole start and the whole descent are literally the same run; only
    the halting transition differs (A2 = 1RZ in BB(3,4), B4 = 1RZ in BB(3,5)),
    so instead of halting, state A reads the 2 and executes A2 = 4LC.

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

From TM35 Require Import Individual35 BB35_rules BB35_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(16, 3, 0) 2 0^inf] in 241 steps.

    The 241 steps are proved in [BB35_start.v], which cuts the run into
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

(** [g15] is made opaque: its value is the third iterate of [g 15], and
    evaluating [g 15] means evaluating a tower of Ackermann-like functions.
    Keeping the constant opaque protects [simpl] and [lia] from unfolding it
    (they then treat it as an atomic natural number). *)
Opaque g15.

(** ** [B_rule] with its result abstracted.

    This is [B_rule] of BB35_rules.v with the (huge) number [Nat.iter n (g k) m]
    replaced by an arbitrary [x].  Instantiating it with [x := g15] lets us
    state the rule with the sealed term, so that no conversion between
    [g15] and the raw term is ever required. *)
Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** The rule at level 15, applied to the configuration reached by the start. *)
Lemma B_rule_15 : Bcfg 16 3 0 (2 >> const 0) -->* Bcfg 16 0 g15 (2 >> const 0).
Proof. apply (B_rule_gen 15 3 0 (2 >> const 0) g15 g15_eq). Qed.

(** The configuration reached after the start and the descent: state A reads
    the 2 that follows the block [3^(2 g15 + 1) 2^16]. *)
Definition c_post : Q * tape := Bcfg 16 0 g15 (2 >> const 0).

Theorem reaches_post : c0 -->* c_post.
Proof.
  eapply evstep_trans; [apply start |].
  apply B_rule_15.
Qed.

(** ** The BB(3,5)-specific tail of the run.

    [desc n m] is the value of the "m" parameter after [n] applications of
    rule 2 (each application also runs the descent [B_rule]); formally

      desc 0 m = m
      desc (S n) m = desc n (g (S n) m)

    which is exactly the sequence of [g]'s that the rule-2 phase applies:
    [g_n], [g_(n-1)], ..., [g_1]. *)
Fixpoint desc (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => desc n' (g (S n') m)
  end.

(** The defining equation of [desc], in a usable form. *)
Lemma desc_S : forall n m, desc (S n) m = desc n (g (S n) m).
Proof. intros n m. reflexivity. Qed.

(** One application of rule 2, followed by the descent [B_rule]: the block of
    2s loses one 2, the block of 3s is reduced to a single 3, and the [g] at
    level [k] is applied to [m]. *)
Lemma rule2_step : forall k m r,
  Bcfg (S (S k)) 0 m (4 >> r) -->* Bcfg (S k) 0 (g (S k) m) (4 >> r).
Proof.
  intros k m r.
  follow (rule2 k m r).
  apply (B_rule_gen k (2 * m + 2) 0 (4 >> r) (g (S k) m)).
  reflexivity.
Qed.

(** The whole rule-2 phase: starting from [B(k, 0, m) 4] with [k = S (S n)],
    the [S n] applications of rule 2 bring the machine down to
    [B(1, 0, desc (S n) m) 4]. *)
Lemma rule2_phase : forall n m r,
  Bcfg (S (S n)) 0 m (4 >> r) -->* Bcfg 1 0 (desc (S n) m) (4 >> r).
Proof.
  intros n m r. revert m r.
  induction n as [|n IH]; intros m r.
  - follow (rule2_step 0 m r).
    replace (desc (S 0) m) with (g (S 0) m) by reflexivity.
    finish_cfg.
  - follow (rule2_step (S n) m r).
    follow (IH (g (S (S n)) m) r).
    replace (desc (S (S n)) m) with (desc (S n) (g (S (S n)) m)) by reflexivity.
    finish_cfg.
Qed.

(** ** The final score.

    The rule-2 phase runs [K+12] times, where [K = 2 g15 + 4]; the "m"
    parameter of the last configuration is [mfin = desc (K+12) 0].

    The two lemmas below are stated for an abstract [x] and only instantiated
    with [g15] afterwards.  That way no tactic ever has to look at [g15],
    which is opaque anyway: [simpl] would otherwise unfold [proj1_sig] and
    then try to evaluate [g 15], which costs exponentially many steps. *)

Definition mfin : nat := desc (2 * g15 + 16) 0.

(** The configuration after rule 1: state A reads the 4 that follows the block
    [3 2^(K+13)]. *)
Definition c_after1 : Q * tape := Bcfg (2 * g15 + 17) 0 0 (4 >> const 0).

Lemma rule1_15_gen : forall (x : nat),
  Bcfg 16 0 x (2 >> const 0) -->* Bcfg (2 * x + 17) 0 0 (4 >> const 0).
Proof.
  intros x.
  follow (rule1 15 x (const 0)).
  replace (S 15 + 2 * x + 1) with (2 * x + 17) by lia.
  apply evstep_refl'; reflexivity.
Qed.

Lemma rule1_15 : Bcfg 16 0 g15 (2 >> const 0) -->* c_after1.
Proof.
  unfold c_after1.
  apply (rule1_15_gen g15).
Qed.

(** The configuration after the rule-2 phase: state A reads the 4 that follows
    the block [3 2], and the "m" parameter is [mfin]. *)
Definition c_after2 : Q * tape := Bcfg 1 0 mfin (4 >> const 0).

Lemma rule2_phase_15_gen : forall (x : nat),
  Bcfg (2 * x + 17) 0 0 (4 >> const 0) -->* Bcfg 1 0 (desc (2 * x + 16) 0) (4 >> const 0).
Proof.
  intros x.
  replace (2 * x + 17) with (S (S (2 * x + 15))) by lia.
  follow (rule2_phase (2 * x + 15) 0 (const 0)).
  replace (S (2 * x + 15)) with (2 * x + 16) by lia.
  apply evstep_refl'; reflexivity.
Qed.

Lemma rule2_phase_15 : c_after1 -->* c_after2.
Proof.
  unfold c_after1, c_after2, mfin.
  apply (rule2_phase_15_gen g15).
Qed.

(** The halting configuration: state B reads a 4, where B4 = 1RZ halts. *)
Definition c_final : Q * tape := ([3]^^(2 * mfin + 3) *> const 0) {{B}}> (4 >> const 0).

Lemma rule3_final_gen : forall (x : nat),
  Bcfg 1 0 x (4 >> const 0) -->* ([3]^^(2 * x + 3) *> const 0) {{B}}> (4 >> const 0).
Proof.
  intros x.
  follow (rule3 x (const 0)).
  finish.
Qed.

Lemma rule3_final : c_after2 -->* c_final.
Proof.
  unfold c_after2, c_final, mfin.
  apply (rule3_final_gen (desc (2 * g15 + 16) 0)).
Qed.

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply reaches_post |].
  eapply evstep_trans; [apply rule1_15 |].
  eapply evstep_trans; [apply rule2_phase_15 |].
  apply rule3_final.
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb35_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.
