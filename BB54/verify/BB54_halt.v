(** * The BB(5,4) machine halts.

    The run has two levels.  After the first D/E phase the machine is in

        B(2X+1, 1, 0) (3 1)^3 0^inf ,     X = g_5(g_4(0)) ,

    a level consists of [T] rounds (a B rule followed by an A3 sweep) and
    ends with the D/E phase again.  The first level has three rounds; its
    D/E phase sees an even number of twos (2X+4), so the machine continues,
    and it produces a right context of (3 1)^(X+2) pairs.  The second level
    has X+2 rounds; its D/E phase sees 2M+1+(X+2) twos, which is odd
    because [X] is even.  The machine therefore arrives in state E on the
    first three of the block of threes, where the halting transition
    E3 = 1RZ applies.

    ** A remark on the style of this file.  Three properties of the Coq
    kernel shape every proof below.

    - The tape is a [Stream], a coinductive type.  The kernel compares two
      streams by unfolding them, and as soon as two streams differ
      syntactically it starts to unfold [pat31], [pat13] and -- inside
      them -- the [g]'s.

    - The kernel *reduces* a fixpoint whenever it has to, and then it digs
      into the stuck argument.  Unfolding [g] never terminates: [g_4 0] is
      evaluated with 2^116 iterations of [g_1], and [g_5 (g_4 0)] has
      infinitely many exposed successors.

    - A [Definition] is unfolded by the kernel as soon as the two sides of
      a comparison differ; a [Notation], in contrast, is expanded when the
      term is parsed, so the kernel never sees the name at all.

    Hence three rules, obeyed everywhere in this file:

    (1) The big numbers are [Notation]s, not [Definition]s, so that the
        two sides of every comparison are literally the same term.

    (2) The big number is always written in the *same* way and is never
        compared with another expression for it.

    (3) Every arithmetic step is done with [rewrite], which replaces a
        term by a syntactically equal one, and never by a conversion.

    The number of twos is therefore always kept in the shape [S (...)] and
    never in the shape [2 * ... + 1]: the latter is a [Nat.add] whose
    first argument is stuck, and the kernel would try to reduce it. *)

From TM54 Require Import Individual54 BB54_rules BB54_run BB54_dphase.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** The big numbers, as notations.

    [X] enters the main regime, [M0] is the number of threes after the
    first level, [M1] the number of threes after the second level, and
    [Xh] is the half of [X]. *)

Notation X := (g 5 (g 4 0)).
Notation Xh := (Nat.div X 2).
Notation M0 := (gchain (2 * X) 3 0).
Notation M1 := (gchain (2 * M0) (S (X + 1)) 0).

(** ** The parity of the [g]'s.

    [g_0(m) = m+1] can be odd, but [g_1(m) = 2m+2] is even, and [g_j(m) =
    g_{j-1}^(2m+2)(0)] is even for every [j >= 1]. *)

Lemma iter_even : forall (f : nat -> nat) n x,
  (forall y, f y mod 2 = 0) -> x mod 2 = 0 -> (Nat.iter n f x) mod 2 = 0.
Proof.
  induction n as [|n IH]; intros x Hf Hx.
  - exact Hx.
  - rewrite Nat.iter_succ. apply Hf.
Qed.

Lemma g1_even : forall y, (g 1 y) mod 2 = 0.
Proof.
  intros y.
  change (Nat.iter (2 * y + 2) (g 0) 0 mod 2 = 0).
  rewrite (iter_g0 (2 * y + 2) 0).
  replace (0 + (2 * y + 2))%nat with ((y + 1) * 2)%nat by lia.
  apply Nat.Div0.mod_mul.
Qed.

Lemma g_even_S : forall j y, (g (S j) y) mod 2 = 0.
Proof.
  induction j as [|j IH]; intros y.
  - apply g1_even.
  - change (Nat.iter (2 * y + 2) (g (S j)) 0 mod 2 = 0).
    apply (iter_even (g (S j)) (2 * y + 2) 0).
    + intros z. apply (IH z).
    + reflexivity.
Qed.

Lemma g_even : forall j y, 1 <= j -> (g j y) mod 2 = 0.
Proof.
  intros j y Hj. destruct j as [|j].
  - lia.
  - apply g_even_S.
Qed.

(** ** Arithmetic on the numbers of twos.

    These are stated abstractly: the tactic [lia] cannot deal with the
    unfolded [g], which it would try to evaluate. *)

Lemma count_one : forall a, 2 * a + 1 = S (2 * a).
Proof. intros a. lia. Qed.

Lemma count_two : forall a, 2 * a + 2 = S (S (2 * a)).
Proof. intros a. lia. Qed.

Lemma count_even : forall a, S (2 * a) + 3 = S (S (2 * (a + 1))).
Proof. intros a. lia. Qed.

Lemma count_odd : forall a b,
  S (2 * a) + (2 * b + 2) = S (S (S (2 * (a + b)))).
Proof. intros a b. lia. Qed.

(** ** The parity of [X] and its half.

    [X] is even, so [X = 2 * (X / 2)]. *)

Lemma X_even : X mod 2 = 0.
Proof. apply (g_even 5 (g 4 0)). lia. Qed.

Lemma X_half : X = 2 * Xh.
Proof.
  assert (Hz : 2 <> 0) by lia.
  assert (Hm : (g 5 (g 4 0)) mod 2 = 0) by (apply g_even; lia).
  assert (H := Nat.div_mod (g 5 (g 4 0)) 2 Hz).
  rewrite Hm in H. clear Hm.
  rewrite Nat.add_0_r in H.
  exact H.
Qed.

(** ** The run.

    [c_score] is the configuration reached by BB54_run.v; it carries the
    sealed number [g40 = g_4(0)]. *)

Lemma c_score_raw : c_score = Bcfg 5 0 (g 4 0) (S3 >> S1 >> Streams.const S0).
Proof.
  unfold c_score. rewrite g40_eq. cbn [Nat.iter g]. reflexivity.
Qed.

(** The state after the first D/E phase of the main regime. *)
Definition c_d1 : Q * tape :=
  Bcfg (2 * X + 1) 1 0 (pat31 3 (Streams.const S0)).

(** The whole run up to the first D/E phase of the main regime. *)
Theorem reaches_d1 : c0 -->* c_d1.
Proof.
  eapply evstep_trans; [apply reaches_score |].
  rewrite c_score_raw.
  apply bb54_dchain.
Qed.

(** The first level: three rounds and then the D/E phase, which sees an even
    number of twos and lets the machine continue. *)
Lemma level0 :
  Bcfg (2 * X + 1) 1 0 (pat31 3 (Streams.const S0)) -->*
  Bcfg (2 * M0 + 1) 1 0 (pat31 (S (X + 1)) (Streams.const S0)).
Proof.
  rewrite (count_one X) at 1.
  eapply evstep_trans.
  - apply (level_gen 3 (2 * X) 0 (Streams.const S0)).
  - rewrite (count_even X).
    apply (D_phase_even (X + 1) M0).
Qed.

(** The second level: [X+2] rounds and then the final B rule. *)
Lemma level1 :
  Bcfg (2 * M0 + 1) 1 0 (pat31 (S (X + 1)) (Streams.const S0)) -->*
  Bcfg (S (2 * M0) + S (X + 1)) 0 M1 (Streams.const S0).
Proof.
  rewrite (count_one M0) at 1.
  apply (level_gen (S (X + 1)) (2 * M0) 0 (Streams.const S0)).
Qed.

(** ** The final count of twos.

    The number of twos at the end is [S (2 * M0) + S (X + 1)].  It is odd
    because [X] is even, and [count_final] rewrites it as
    [S (S (S (2 * (M0 + Nat.div X 2))))], the shape expected by
    [D_phase_odd].

    The arithmetic is done by [count_final_gen], which is stated for
    *variables* [a] and [b].  This matters: with variables the kernel
    cannot reduce anything, while with the big numbers it would try to
    reduce them, and reducing them never terminates. *)

Lemma count_two_S : forall a, S (S (2 * a)) = 2 * a + 2.
Proof. intros a. lia. Qed.

Lemma count_final_gen : forall a b,
  b mod 2 = 0 ->
  S (2 * a) + S (b + 1) = S (S (S (2 * (a + Nat.div b 2)))).
Proof.
  intros a b Hb.
  assert (Hz : 2 <> 0) by lia.
  assert (H := Nat.div_mod b 2 Hz).
  rewrite Hb in H. clear Hb.
  rewrite Nat.add_0_r in H.
  rewrite H at 1.
  rewrite (count_one (Nat.div b 2)).
  rewrite (count_two_S (Nat.div b 2)).
  apply (count_odd a (Nat.div b 2)).
Qed.

Lemma count_final :
  S (2 * M0) + S (X + 1) = S (S (S (2 * (M0 + Nat.div X 2)))).
Proof.
  apply (count_final_gen M0 X X_even).
Qed.

Theorem bb54_halt :
  c0 -->* (E;; (([S3] ^^ (2 * M1) *> Streams.const S0) {{ S3 }}
               (S3 >> pat13 (S (M0 + Nat.div X 2)) (S1 >> Streams.const S0)))).
Proof.
  eapply evstep_trans; [apply reaches_d1 |].
  eapply evstep_trans; [apply level0 |].
  eapply evstep_trans; [apply level1 |].
  rewrite (count_final) at 1.
  apply (D_phase_odd (M0 + Nat.div X 2) M1).
Qed.

(** ** The sigma at halting.

    The tape of the final configuration is

      0^inf  3^(2 M1)  E>  3  (1 3)^(M0 + X/2 + 1)  1  0^inf ,

    the head being on the first three of the block of threes (and the
    machine being in state E, which halts).  Its nonzero cells are

      2 M1  +  1  +  1  +  2 (M0 + X/2 + 1)  +  1
        =  2 M1 + 2 M0 + X + 5 .

    ** Sealed aliases.  The kernel must never *reduce* the big numbers:
    they contain [g], and reducing [g] never terminates -- not even the
    kernel's type checker may look at them, e.g. when it computes the
    length of a block of the form [[S3] ^^ (2 * M1)].  The aliases below
    are therefore declared [Opaque]; the equalities that connect them
    with the explicit terms are proved before they are sealed. *)

Definition M0s : nat := gchain (2 * X) 3 0.
Lemma M0s_eq : M0s = gchain (2 * X) 3 0.
Proof. reflexivity. Qed.
Opaque M0s.

Definition M1s : nat := gchain (2 * M0s) (S (X + 1)) 0.
Lemma M1s_eq : M1s = gchain (2 * M0s) (S (X + 1)) 0.
Proof. reflexivity. Qed.
Opaque M1s.

Definition sigma_final : nat := 2 * M1s + 2 * M0s + 2 * (Nat.div X 2) + 5.

(** The nonzero cells of the tape of the final configuration, from left to
    right. *)
Definition final_cells : list sym :=
  [S3]^^(2 * M1s) ++ [S3; S3] ++ ([S1; S3])^^(M0s + Nat.div X 2 + 1) ++ [S1].

(** The counting lemma is stated for abstract numbers, and only afterwards
    instantiated with the big ones. *)
Lemma cells_count_final : forall a b c : nat,
  length ([S3]^^(2 * a) ++ [S3; S3] ++ ([S1; S3])^^(b + c + 1) ++ [S1])
  = 2 * a + 2 * b + 2 * c + 5.
Proof.
  intros a b c.
  rewrite !app_length.
  rewrite (lpow_length (2 * a) [S3]).
  rewrite (lpow_length (b + c + 1) [S1; S3]).
  cbn [length]. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma_final.
Proof.
  unfold final_cells, sigma_final.
  apply cells_count_final.
Qed.

(** The same number with [X] instead of its half.

    The lemma is again stated for variables: a [rewrite] with the pattern
    [X] would have to look at the candidates of the goal, and the kernel
    would then try to reduce them -- and reducing [X] never terminates. *)
Lemma sigma_final_eq_gen : forall (a b x : nat),
  x mod 2 = 0 ->
  2 * a + 2 * b + x + 5 = 2 * a + 2 * b + 2 * (Nat.div x 2) + 5.
Proof.
  intros a b x Hx.
  assert (Hz : 2 <> 0) by lia.
  assert (H := Nat.div_mod x 2 Hz).
  rewrite Hx in H. clear Hx.
  rewrite Nat.add_0_r in H.
  rewrite <- H. reflexivity.
Qed.

Lemma sigma_final_eq : 2 * M1s + 2 * M0s + X + 5 = sigma_final.
Proof.
  unfold sigma_final.
  apply (sigma_final_eq_gen M1s M0s X X_even).
Qed.

(** Every cell of [final_cells] is nonzero. *)
Lemma final_cells_nonblank : forall (y : sym), In y final_cells -> y <> S0.
Proof.
  intros y H.
  unfold final_cells in H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + simpl in H. intuition congruence.
    + apply in_app_or in H as [H | H].
      * apply in_lpow in H. simpl in H. intuition congruence.
      * simpl in H. intuition congruence.
Qed.

(** The run of the machine, and its sigma, in one statement.

    The first component is [bb54_halt] itself, with the explicit terms;
    the second one counts the nonzero cells of its tape, with the sealed
    aliases [M1s], [M0s] (which equal the explicit ones by [M1s_eq] and
    [M0s_eq]). *)
Theorem bb54_halt_main :
  c0 -->* (E;; (([S3] ^^ (2 * M1) *> Streams.const S0) {{ S3 }}
               (S3 >> pat13 (S (M0 + Nat.div X 2)) (S1 >> Streams.const S0))))
  /\ length final_cells = sigma_final.
Proof.
  split; [apply bb54_halt | exact final_cells_count].
Qed.
