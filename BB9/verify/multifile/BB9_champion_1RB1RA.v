(** * The BB(9) champion 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH halts *)

(** Machine-checked halting proof of the 9-state, 2-symbol champion found by Jacobzheng (wiki "Champions" table,
    claimed bound > f_omega(f_9(2))).  Written for the bbchallenge investigation in
    bb8_list/investigations/bb9_champion_1RB1RA0LC0LF.md.

    Configuration family (head D on the blank left of the word; the word is read towards the right):
      Kd ds a b = 0^inf <D 1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 0 ... 1^d_n 0^inf        ds = [d_1; ...; d_n], top digit first
    Rules, proved for all parameters (the machine is a digit-list counter of Ackermann type):
      R1 : Kd ds (S a) b                               -->+ Kd ds a (b + 3)
      R2 : Kd (S y :: t) 0 b                           -->+ Kd (y :: t) (b + 2) 1
      R3 : Kd (0^(m+1) ++ S y :: t) 0 (2(m+1) + s)     -->+ Kd (2^m ++ (s+2) :: y :: t) 2 1
      R4e: Kd (0^k) 0 (2m)                             -->+ Kd (Q m) 1 0      Q m = (0,1)^m (0,2)
      R4o: Kd (0^k) 0 (2m+1) halts (7 steps after the fill loop; E0 = 1RZ)
    The invariant 2j <= b (j = number of zero digits above the digit being cleared) keeps R3 applicable (lemma [CDP_all]);
    clearing a digit v at depth j maps b to a larger b' with b' = b + v (mod 2), and for j >= 1 b' mod 4 depends only on
    b + v mod 2 (3 if odd, 0 if even).  The blank tape reaches Kd [] 2 0 in 11 steps, then R1,R1 and R4e (m = 3).
    The first clearing of Q 3 from b = 3 (pairs: 3+1 even -> 0, then 3, then 0, then the digit 2 -> 0) gives b = 0 mod 4,
    so the second restart has m even and the second clearing from b = 3 ends with b odd: R4o halts. *)

From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, A)
  | B, 0 => Some (0, L, C)  | B, 1 => Some (0, L, F)
  | C, 0 => Some (0, R, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, R, G)
  | E, 0 => None            | E, 1 => Some (0, R, A)
  | F, 0 => Some (1, L, B)  | F, 1 => Some (1, L, F)
  | G, 0 => Some (1, L, H)  | G, 1 => Some (1, R, E)
  | H, 0 => Some (0, L, I)  | H, 1 => Some (1, L, H)
  | I, 0 => Some (1, L, B)  | I, 1 => Some (0, L, H)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

Lemma cr_AR_1_1 : forall n l r, l {{A}}> [1]^^n *> r -->* [1]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_1_1 : forall n l r, [1]^^n *> l <{{F}} r -->* l <{{F}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_CL_1_1 : forall n l r, [1]^^n *> l <{{C}} r -->* l <{{C}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_011_101 : forall n l r, [0;1;1]^^n *> l <{{F}} r -->* l <{{F}} [1;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_IL_110_010 : forall n l r, [1;1;0]^^n *> l <{{I}} r -->* l <{{I}} [0;1;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma R1 : forall b a l, const 0 <{{D}} (1 >> [1]^^b *> 0 >> 1 >> [1]^^a *> l) -->+ const 0 <{{D}} (1 >> 1 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^a *> l).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  execute.
  follow cr_FL_1_1.
  do 5 step. finish_norm.
Qed.

Lemma R2 : forall b y t, const 0 <{{D}} (1 >> [1]^^b *> 0 >> 0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{D}} (1 >> 1 >> 0 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  execute.
  follow cr_CL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_AR_1_1.
  execute.
  follow cr_FL_1_1.
  do 6 step. finish_norm.
Qed.

Lemma ENTRY : forall b w, const 0 <{{D}} (1 >> [1]^^b *> 0 >> w) -->+ ([1]^^b *> 1 >> 1 >> const 0) {{A}}> (0 >> w).
Proof.
  intros.
  start_progress.
  follow cr_AR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma LOOP : forall r Y z, (1 >> 1 >> [1]^^r *> 0 >> Y) {{A}}> (0 >> 0 >> z) -->+ ([1]^^r *> 0 >> 1 >> 1 >> 0 >> Y) {{A}}> (0 >> z).
Proof.
  intros.
  start_progress.
  follow cr_CL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_AR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma FINAL : forall s m y t, ([1]^^s *> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{A}}> (0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{D}} (1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_FL_1_1.
  execute.
  follow cr_FL_011_101.
  do 3 step. finish_norm.
Qed.

Lemma R4E : forall i, ([0;1;1]^^i *> const 0) {{A}}> const 0 -->+ const 0 <{{D}} (1 >> [0;1;0]^^i *> 0 >> 1 >> 1 >> const 0).
Proof.
  intros.
  start_progress.
  rewrite (align_lpow_const 0 [1;1] _). simpl app.
  execute.
  follow cr_IL_110_010.
  do 3 step. finish_norm.
Qed.


(** ** The digit family *)

Fixpoint lft (ds : list nat) : side :=
  match ds with
  | [] => const 0
  | d :: t => 0 >> [1]^^d *> lft t
  end.

(** Kd ds a b = 0^inf <D (1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 ...) : the head is on the blank left of the word *)
Definition Kd (ds : list nat) (a b : nat) : Q * tape :=
  const 0 <{{D}} (1 >> [1]^^b *> 0 >> [1]^^a *> lft ds).

Lemma zeros_shift : forall j l, [0]^^j *> 0 >> l = 0 >> [0]^^j *> l.
Proof. induction j; intros. - reflexivity. - simpl. rewrite IHj. reflexivity. Qed.

Lemma zeros_const : forall j, [0]^^j *> const 0 = const 0.
Proof. induction j. - reflexivity. - simpl. rewrite IHj. symmetry. apply const_unfold. Qed.

Lemma lft_zeros : forall k t, lft (repeat 0%nat k ++ t) = [0]^^k *> lft t.
Proof. induction k; intros. - reflexivity. - simpl. rewrite IHk. reflexivity. Qed.

Lemma lft_blank : forall k, lft (repeat 0%nat k) = const 0.
Proof. intros. rewrite <- (app_nil_r (repeat 0%nat k)), lft_zeros. apply zeros_const. Qed.

Lemma lft_twos : forall k t, lft (repeat 2%nat k ++ t) = [0;1;1]^^k *> lft t.
Proof. induction k; intros. - reflexivity. - simpl. rewrite IHk. reflexivity. Qed.

Lemma repeat_snoc : forall (x : nat) n U, repeat x n ++ x :: U = repeat x (S n) ++ U.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

(** ** The four rules *)

Lemma KR1 : forall ds a b, Kd ds (S a) b -->+ Kd ds a (b + 3).
Proof.
  intros. unfold Kd. replace (b + 3) with (3 + b) by lia.
  apply R1.
Qed.

Lemma KR2 : forall y t b, Kd (S y :: t) 0 b -->+ Kd (y :: t) (b + 2) 1.
Proof.
  intros. unfold Kd. replace (b + 2) with (2 + b) by lia.
  apply R2.
Qed.

Lemma const0 : 0 >> const 0 = const 0.
Proof. symmetry. apply const_unfold. Qed.

Lemma lpow_ones_two : forall n X, [1]^^n *> 1 >> 1 >> X = [1]^^(n + 2) *> X.
Proof. induction n; intros. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Lemma blocks_snoc : forall i Y, [0;1;1]^^i *> 0 >> 1 >> 1 >> 0 >> Y = [0;1;1]^^(S i) *> 0 >> Y.
Proof. intros. change (0 >> 1 >> 1 >> 0 >> Y) with ([0;1;1] *> 0 >> Y). rewrite lpow_shift'. reflexivity. Qed.

Lemma ones_back : forall s X, [1]^^s *> 1 >> X = 1 >> [1]^^s *> X.
Proof. intros. change (1 >> X) with ([1] *> X). rewrite lpow_shift'. reflexivity. Qed.

(** The cycle LOOP, i times. *)
Lemma LOOPS : forall i s Y z,
  ([1]^^(2 * i + s) *> 0 >> Y) {{A}}> ([0]^^i *> 0 >> z) -->*
  ([1]^^s *> [0;1;1]^^i *> 0 >> Y) {{A}}> (0 >> z).
Proof.
  induction i; intros.
  - finish.
  - replace (2 * S i + s) with (S (S (2 * i + s))) by lia.
    change ([1]^^(S (S (2 * i + s))) *> 0 >> Y) with (1 >> 1 >> [1]^^(2 * i + s) *> 0 >> Y).
    change ([0]^^(S i) *> 0 >> z) with (0 >> [0]^^i *> 0 >> z).
    rewrite zeros_shift.
    eapply evstep_trans; [apply progress_evstep, LOOP |].
    rewrite <- zeros_shift.
    follow (IHi s (1 >> 1 >> 0 >> Y) z).
    apply evstep_refl'. rewrite blocks_snoc. reflexivity.
Qed.

Lemma EQ3 : forall m s y t,
  1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t =
  1 >> [1]^^1 *> 0 >> [1]^^2 *> ([0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
Proof.
  intros.
  rewrite (align_lpow 1 [0;1] _ m). simpl app.
  change (0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t)
    with ([0;1;1] *> (0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t)).
  rewrite lpow_shift'.
  rewrite ones_back.
  change (1 >> 1 >> [1]^^s *> 0 >> [1]^^y *> t) with ([1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  change (1 >> [1]^^1 *> 0 >> [1]^^2 *> ([0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t))
    with (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  change (0 >> 1 >> 1 >> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t)
    with ([0;1;1] *> [0;1;1]^^m *> 0 >> [1]^^(S (S s)) *> 0 >> [1]^^y *> t).
  reflexivity.
Qed.

Lemma KR3 : forall m s y t,
  Kd (repeat 0%nat (S m) ++ S y :: t) 0 (2 * S m + s) -->+ Kd (repeat 2%nat m ++ S (S s) :: y :: t) 2 1.
Proof.
  intros m s y t. unfold Kd. rewrite lft_zeros.
  change ([1]^^0 *> [0]^^(S m) *> lft (S y :: t)) with ([0]^^(S m) *> 0 >> 1 >> [1]^^y *> lft t).
  eapply progress_evstep_trans; [apply ENTRY |].
  replace ([1]^^(2 * S m + s) *> 1 >> 1 >> const 0) with ([1]^^(2 * S (S m) + s) *> 0 >> const 0).
  2:{ rewrite lpow_ones_two, const0. replace (2 * S (S m) + s) with (2 * S m + s + 2) by lia. reflexivity. }
  change (0 >> [0]^^(S m) *> 0 >> 1 >> [1]^^y *> lft t) with ([0]^^(S (S m)) *> 0 >> 1 >> [1]^^y *> lft t).
  follow (LOOPS (S (S m)) s (const 0) (1 >> [1]^^y *> lft t)).
  simpl lpow. rewrite const0.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply FINAL |].
  apply evstep_refl'. unfold Kd. rewrite lft_twos. simpl lft.
  rewrite EQ3. reflexivity.
Qed.

(** The restart list: m pairs (0,1) on top of the pair (0,2); top digit first. *)
Fixpoint Q (m : nat) : list nat :=
  match m with
  | O => [0%nat; 2%nat]
  | S m' => 0%nat :: 1%nat :: Q m'
  end.

Lemma lft_Q : forall m, lft (Q m) = [0;0;1]^^m *> 0 >> 0 >> 1 >> 1 >> const 0.
Proof. induction m. - reflexivity. - simpl. simpl in IHm. rewrite IHm. reflexivity. Qed.

Lemma EQ4 : forall m Z, 0 >> [0;1;0]^^m *> Z = [0;0;1]^^m *> 0 >> Z.
Proof. intros. rewrite (align_lpow 0 [0;1] _ m). simpl app. reflexivity. Qed.

Lemma LOOPS_blank : forall i s,
  ([1]^^(2 * i + s) *> const 0) {{A}}> const 0 -->*
  ([1]^^s *> [0;1;1]^^i *> const 0) {{A}}> const 0.
Proof.
  intros. pose proof (LOOPS i s (const 0) (const 0)) as H.
  rewrite zeros_shift, zeros_const, const0 in H. exact H.
Qed.

Lemma KR4E : forall k m, Kd (repeat 0%nat k) 0 (2 * m) -->+ Kd (Q m) 1 0.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (2 * m + 2) with (2 * S m + 0) by lia.
  follow (LOOPS_blank (S m) 0).
  simpl lpow.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply (R4E (S m)) |].
  apply evstep_refl'. unfold Kd. rewrite lft_Q. simpl lpow.
  cbn [Str_app]. rewrite EQ4. reflexivity.
Qed.

(** Odd b: the machine halts. *)
Lemma HALT7 : forall m, exists c, (1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{A}}> const 0 -->* c /\ halted tm c.
Proof.
  intros. eexists. split.
  - do 7 step. apply evstep_refl.
  - simpl. reflexivity.
Qed.

Lemma KR4O : forall k m, exists c, Kd (repeat 0%nat k) 0 (2 * m + 1) -->* c /\ halted tm c.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  destruct (HALT7 m) as [c [H1 H2]].
  exists c. split; [| exact H2].
  apply progress_evstep.
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (2 * m + 1 + 2) with (2 * S m + 1) by lia.
  follow (LOOPS_blank (S m) 1).
  simpl lpow.
  exact H1.
Qed.

Lemma init_reach : c0 -->* Kd [] 2 0.
Proof. unfold Kd. simpl. do 11 step. finish. Qed.

(** ** Clearing digits (abstract level) *)

Local Open Scope nat_scope.

Ltac absmod x k :=
  let q := fresh "q" in let r := fresh "r" in
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x k) as H1;
  assert (H2 : x mod k < k) by (apply Nat.mod_upper_bound; discriminate);
  set (q := x / k) in *; set (r := x mod k) in *; clearbody q r.
(** lia in this Coq build does not understand mod: abstract each x mod k with its division facts first. *)
Ltac mods :=
  repeat match goal with
  | H : context[?x mod ?k] |- _ => absmod x k
  | |- context[?x mod ?k] => absmod x k
  end.

Lemma R1iter : forall a ds b, Kd ds a b -->* Kd ds 0 (b + 3 * a).
Proof.
  induction a; intros.
  - replace (b + 3 * 0) with b by lia. finish.
  - eapply evstep_trans; [apply progress_evstep, KR1 |].
    follow (IHa ds (b + 3)).
    replace (b + 3 * S a) with (b + 3 + 3 * a) by lia. finish.
Qed.

(** Counting the top digit down to 0 (depth 0): each unit maps b to 3b+7. *)
Lemma CH : forall v U B, exists B',
  Kd (v :: U) 0 B -->* Kd (0 :: U) 0 B' /\
  B + 7 * v <= B' /\ B' mod 2 = (B + v) mod 2 /\ (v = 0 -> B' = B) /\
  (B mod 4 = 3 -> (v mod 2 = 0 -> B' mod 4 = 3) /\ (v mod 2 = 1 -> B' mod 4 = 0)) /\
  (B mod 4 = 0 -> (v mod 2 = 0 -> B' mod 4 = 0) /\ (v mod 2 = 1 -> B' mod 4 = 3)).
Proof.
  induction v; intros U B.
  - exists B. split; [finish |]. mods; lia.
  - destruct (IHv U (1 + 3 * (B + 2))) as [B' [H1 [H2 [H3 [Hz [H4 H5]]]]]].
    exists B'. split.
    + eapply evstep_trans; [apply progress_evstep, KR2 |].
      follow (R1iter (B + 2) (v :: U) 1). exact H1.
    + mods; lia.
Qed.
From Coq Require Import Wf_nat.

(** Clearing one digit v at depth j (j zeros above it): the invariant 2j <= b keeps R3 applicable. *)
Definition CDP (j : nat) : Prop := forall v U B, 2 * j <= B ->
  exists B', Kd (repeat 0 j ++ v :: U) 0 B -->* Kd (repeat 0 (S j) ++ U) 0 B' /\
    B <= B' /\ (v = 0 -> B' = B) /\ (1 <= v -> B + v + 2 * j + 5 <= B') /\
    B' mod 2 = (B + v) mod 2 /\
    (1 <= j -> 1 <= v -> ((B + v) mod 2 = 0 -> B' mod 4 = 0) /\ ((B + v) mod 2 = 1 -> B' mod 4 = 3)).

(** A block of n twos on top, cleared from depth t, below depth D. *)
Lemma BLK : forall D, (forall j', j' < D -> CDP j') ->
  forall n t V X, t + n <= D -> 2 * t <= X ->
  exists X', Kd (repeat 0 t ++ repeat 2 n ++ V) 0 X -->* Kd (repeat 0 (t + n) ++ V) 0 X' /\
    X + 7 * n <= X' /\ 2 * (t + n) <= X' /\ X' mod 2 = X mod 2 /\ (n = 0 -> X' = X).
Proof.
  intros D HD. induction n as [| n IHn]; intros t V X Hd Hx.
  - exists X. replace (t + 0) with t by lia. split; [simpl; finish |]. repeat split; try lia.
  - destruct (HD t ltac:(lia) 2 (repeat 2 n ++ V) X Hx) as [X1 [H1 [H2 [H3 [H4 [H5 _]]]]]].
    specialize (H4 ltac:(lia)).
    destruct (IHn (S t) V X1 ltac:(lia) ltac:(lia)) as [X' [H6 [H7 [H8 [H9 H10]]]]].
    exists X'. split.
    + eapply evstep_trans; [exact H1 |]. replace (t + S n) with (S t + n) by lia. exact H6.
    + repeat split; try (mods; lia).
Qed.

Lemma CDP_all : forall j, CDP j.
Proof.
  intro j. induction j as [j IH] using lt_wf_ind.
  destruct j as [| n].
  - intros v U B _. destruct (CH v U B) as [B' [H1 [H2 [H3 [Hz [H4 H5]]]]]].
    exists B'. split; [exact H1 |].
    mods; lia.
  - intro v. induction v as [| w IHw]; intros U B HB.
    + exists B. split.
      * rewrite repeat_snoc. finish.
      * mods; lia.
    + remember (B - 2 * S n) as s eqn:Hs.
      assert (HB' : B = 2 * S n + s) by lia.
      assert (Hr : Kd (repeat 0 (S n) ++ S w :: U) 0 B -->*
                   Kd (repeat 2 n ++ S (S s) :: w :: U) 0 7).
      { rewrite HB'. eapply evstep_trans; [apply progress_evstep, KR3 |].
        follow (R1iter 2 (repeat 2 n ++ S (S s) :: w :: U) 1). finish. }
      destruct (BLK (S n) IH n 0 (S (S s) :: w :: U) 7 ltac:(lia) ltac:(lia))
        as [X [H1 [H2 [H3 [H4 H5]]]]].
      assert (Hd : exists B1, Kd (repeat 0 n ++ S (S s) :: w :: U) 0 X -->* Kd (repeat 0 (S n) ++ w :: U) 0 B1 /\
          X + S (S s) + 2 * n + 5 <= B1 /\ B1 mod 2 = (X + S (S s)) mod 2 /\
          ((s mod 2 = 0 -> B1 mod 4 = 3) /\ (s mod 2 = 1 -> B1 mod 4 = 0))).
      { destruct n as [| n'].
        - specialize (H5 eq_refl). subst X.
          destruct (CH (S (S s)) (w :: U) 7) as [B1 [G1 [G2 [G3 [Gz [G4 G5]]]]]].
          exists B1. split; [exact G1 |]. mods; lia.
        - destruct (IH (S n') ltac:(lia) (S (S s)) (w :: U) X ltac:(lia)) as [B1 [G1 [G2 [G3 [G4 [G5 G6]]]]]].
          exists B1. split; [exact G1 |].
          specialize (G4 ltac:(lia)). specialize (G6 ltac:(lia) ltac:(lia)). mods; lia. }
      destruct Hd as [B1 [Hd1 [Hd2 [Hd3 Hd4]]]].
      destruct (IHw U B1 ltac:(lia)) as [B' [I1 [I2 [I3 [I4 [I5 I6]]]]]].
      exists B'. split.
      * eapply evstep_trans; [exact Hr |]. eapply evstep_trans; [exact H1 |].
        eapply evstep_trans; [exact Hd1 |]. exact I1.
      * destruct w as [| w'].
        -- specialize (I3 eq_refl). mods; lia.
        -- specialize (I4 ltac:(lia)). specialize (I6 ltac:(lia) ltac:(lia)). mods; lia.
Qed.

(** ** The restart list Q m = (0,1)^m (0,2): one pair at a time *)

Fixpoint pairs (m : nat) (V : list nat) : list nat :=
  match m with
  | O => V
  | S m' => 0 :: 1 :: pairs m' V
  end.

Lemma Q_pairs : forall m, Q m = pairs m [0; 2].
Proof. induction m. - reflexivity. - simpl. rewrite IHm. reflexivity. Qed.

Lemma PAIR : forall j V B, 2 * (j + 1) <= B ->
  exists B', Kd (repeat 0 j ++ 0 :: 1 :: V) 0 B -->* Kd (repeat 0 (j + 2) ++ V) 0 B' /\
    B + 2 * j + 8 <= B' /\ B' mod 2 = (B + 1) mod 2 /\
    ((B + 1) mod 2 = 0 -> B' mod 4 = 0) /\ ((B + 1) mod 2 = 1 -> B' mod 4 = 3).
Proof.
  intros j V B HB.
  destruct (CDP_all (S j) 1 V B ltac:(lia)) as [B' [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  specialize (H4 ltac:(lia)). specialize (H6 ltac:(lia) ltac:(lia)).
  exists B'. split.
  - rewrite repeat_snoc. replace (j + 2) with (S (S j)) by lia. exact H1.
  - mods; lia.
Qed.

Lemma PAIRS : forall m j V B, 2 * (j + 1) <= B ->
  exists B', Kd (repeat 0 j ++ pairs m V) 0 B -->* Kd (repeat 0 (j + 2 * m) ++ V) 0 B' /\
    2 * (j + 2 * m + 1) <= B' /\ B' mod 2 = (B + m) mod 2.
Proof.
  induction m; intros j V B HB.
  - exists B. split; [| split; [lia | mods; lia]].
    replace (j + 2 * 0) with j by lia. finish.
  - destruct (PAIR j (pairs m V) B HB) as [B1 [H1 [H2 [H3 [H4 H5]]]]].
    destruct (IHm (j + 2) V B1 ltac:(lia)) as [B' [I1 [I2 I3]]].
    exists B'. split.
    + eapply evstep_trans; [exact H1 |].
      replace (j + 2 * S m) with (j + 2 + 2 * m) by lia. exact I1.
    + split; [replace (j + 2 * S m) with (j + 2 + 2 * m) by lia; lia | mods; lia].
Qed.

Lemma LAST : forall j B, 2 * (j + 1) <= B ->
  exists B', Kd (repeat 0 j ++ [0; 2]) 0 B -->* Kd (repeat 0 (j + 2)) 0 B' /\
    B' mod 2 = B mod 2 /\
    ((B + 2) mod 2 = 0 -> B' mod 4 = 0) /\ ((B + 2) mod 2 = 1 -> B' mod 4 = 3).
Proof.
  intros j B HB.
  destruct (CDP_all (S j) 2 [] B ltac:(lia)) as [B' [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  specialize (H6 ltac:(lia) ltac:(lia)).
  exists B'. split.
  - rewrite repeat_snoc. replace (j + 2) with (S (S j)) by lia.
    rewrite app_nil_r in H1. exact H1.
  - mods; lia.
Qed.

Lemma halt_from_zeros : forall k B, B mod 2 = 1 ->
  exists c, Kd (repeat 0 k) 0 B -->* c /\ halted tm c.
Proof.
  intros k B HB.
  assert (HB' : B = 2 * (B / 2) + 1) by (mods; lia).
  pose proof (KR4O k (B / 2)) as H. rewrite <- HB' in H. exact H.
Qed.

Lemma rebuild_from_zeros : forall k B, B mod 4 = 0 ->
  exists m, Kd (repeat 0 k) 0 B -->+ Kd (Q (2 * m)) 1 0.
Proof.
  intros k B HB. exists (B / 4).
  assert (HB' : B = 2 * (2 * (B / 4))) by (mods; lia).
  pose proof (KR4E k (2 * (B / 4))) as H. rewrite <- HB' in H. exact H.
Qed.

(** ** The run *)

Theorem halt : halts tm c0.
Proof.
  (* from the blank tape to Kd [] 2 0, then two R1 and the first rebuild (b = 6, m = 3) *)
  assert (H0 : c0 -->* Kd (Q 3) 0 3).
  { follow init_reach.
    follow (R1iter 2 [] 0).
    change (Kd [] 0 (0 + 3 * 2)) with (Kd (repeat 0 0) 0 (2 * 3)).
    eapply evstep_trans; [apply progress_evstep, (KR4E 0 3) |].
    eapply evstep_trans; [apply progress_evstep, (KR1 (Q 3) 0 0) |]. finish. }
  (* first clearing: b = 3, three (0,1) pairs and (0,2); mod 4 bookkeeping *)
  destruct (PAIR 0 (pairs 2 [0; 2]) 3 ltac:(lia)) as [B1 [A1 [A2 [A3 [A4 A5]]]]].
  destruct (PAIR 2 (pairs 1 [0; 2]) B1 ltac:(lia)) as [B2 [C1 [C2 [C3 [C4 C5]]]]].
  destruct (PAIR 4 (pairs 0 [0; 2]) B2 ltac:(lia)) as [B3 [D1 [D2 [D3 [D4 D5]]]]].
  destruct (LAST 6 B3 ltac:(lia)) as [B4 [E1 [E2 [E3 E4]]]].
  assert (HB4 : B4 mod 4 = 0) by (mods; lia).
  assert (H1 : c0 -->* Kd (repeat 0 8) 0 B4).
  { follow H0. rewrite Q_pairs. simpl pairs.
    follow A1. follow C1. follow D1. follow E1. finish. }
  destruct (rebuild_from_zeros 8 B4 HB4) as [m Hm].
  (* second clearing: b = 3 again, 2m pairs and (0,2); the final b is odd *)
  destruct (PAIRS (2 * m) 0 [0; 2] 3 ltac:(lia)) as [B5 [F1 [F2 F3]]].
  destruct (LAST (0 + 2 * (2 * m)) B5 ltac:(lia)) as [B6 [G1 [G2 [G3 G4]]]].
  assert (HB6 : B6 mod 2 = 1) by (mods; lia).
  destruct (halt_from_zeros (0 + 2 * (2 * m) + 2) B6 HB6) as [c [Hc1 Hc2]].
  assert (Hrun : c0 -->* c).
  { follow H1. eapply evstep_trans; [apply progress_evstep, Hm |].
    eapply evstep_trans; [apply progress_evstep, (KR1 (Q (2 * m)) 0 0) |].
    rewrite Q_pairs. 
    replace (0 + 3) with 3 by lia.
    follow F1. follow G1. exact Hc1. }
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. exact Hc2.
Qed.
