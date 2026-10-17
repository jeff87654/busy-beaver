(** * The 9-state machine 1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA halts *)

(** Machine-checked halting proof of the 9-state, 2-symbol machine achieving sigma > f_omega(f_omega(465009)).
    In the state labels of BB9_champion_1RB1RA.v (A..I), this machine is:
      1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RH0RA_1LB1LF_1RZ1RE_1LI1LI_0RE0LH   (started in state E)
    Relabeled to standard Tree Normal Form (first-visit order E->A, H->B, I->C, A->D, B->E, F->F, C->G, D->H, G->I):
      1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA   (started in state A)

    Configuration family (head H on the blank left of the word; the word is read towards the right):
      Kd ds a b = 0^inf <H 1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 0 ... 1^d_n 0^inf        ds = [d_1; ...; d_n], top digit first
    Rules, proved for all parameters:
      R1   : Kd ds (S a) b                           -->+ Kd ds a (b + 3)
      R2   : Kd (S y :: t) 0 b                       -->+ Kd (y :: t) (b + 2) 1
      R3   : Kd (0^(m+1) ++ S y :: t) 0 (2(m+1) + s) -->+ Kd (2^m ++ (s+2) :: y :: t) 2 1
      R4O3 : Kd (0^k) 0 (4m + 3)                     -->+ Kd (2 :: trip m) 0 1,   trip m = (0,1,2)^m (0,1,1)
      R4Ex : Kd (0^k) 0 (2m) halts in 5 steps after the fill loop (I0 = 1RZ)

    The run executes three cascades (two deep f_omega cascades):
      1. The blank tape reaches Kd [1; 1] 0 1 in 49 steps; clearing [1; 1] gives b1 = U 1 10 = 620011 = 4 * 155002 + 3.
      2. Rebuild 1 (m1 = 155002, even) gives Kd (2 :: trip 155002) 0 1; clearing it reaches depth 465009 and gives
         b2 = Tv 155002 1 37 with b2 mod 8 = 7 (since m1 is even, the counter before the last two 1-digits is odd,
         so U (3m1+2) sends it to 0 mod 8 and U (3m1+3) sends that to 7 mod 8).
      3. Rebuild 2 has m2 = b2 / 4 odd; clearing Kd (2 :: trip m2) 0 1 flips parity 3m2 + 4 times from b = 1,
         ending with b3 = Tv m2 1 37 even; R4Ex halts on I0 = 1RZ. *)

From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, D)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (1, L, C)
  | C, 0 => Some (0, R, A)  | C, 1 => Some (0, L, B)
  | D, 0 => Some (1, R, E)  | D, 1 => Some (1, R, D)
  | E, 0 => Some (0, L, G)  | E, 1 => Some (0, L, F)
  | F, 0 => Some (1, L, E)  | F, 1 => Some (1, L, F)
  | G, 0 => Some (0, R, H)  | G, 1 => Some (1, L, G)
  | H, 0 => Some (1, R, D)  | H, 1 => Some (1, R, I)
  | I, 0 => None            | I, 1 => Some (1, R, A)
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

Lemma cr_DR_1_1 : forall n l r, l {{D}}> [1]^^n *> r -->* [1]^^n *> l {{D}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_1_1 : forall n l r, [1]^^n *> l <{{F}} r -->* l <{{F}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_GL_1_1 : forall n l r, [1]^^n *> l <{{G}} r -->* l <{{G}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_FL_011_101 : forall n l r, [0;1;1]^^n *> l <{{F}} r -->* l <{{F}} [1;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** The rebuild pass: every 20 steps, A shifts left across two (110)-blocks and emits 110010 on the right. *)
Lemma cr_AL_6 : forall n l r,
  (1 >> 1 >> 0 >> [1;1;0;1;1;0]^^n *> l) {{A}}> (0 >> 1 >> r) -->*
  (1 >> 1 >> 0 >> l) {{A}}> (0 >> [1;1;0;0;1;0]^^n *> 1 >> r).
Proof. induction n; intros. - finish. - do 20 step. follow IHn. finish_norm. Qed.

Lemma R4O3 : forall m,
  (1 >> [0;1;1;0;1;1]^^(S m) *> const 0) {{D}}> const 0 -->+
  const 0 <{{H}} (1 >> 1 >> 0 >> 0 >> 1 >> 1 >> [0;0;1;0;1;1]^^m *> 0 >> 0 >> 1 >> 0 >> 1 >> const 0).
Proof.
  intros.
  start_progress.
  rewrite align_lpow_const. simpl app.
  do 3 step.
  follow cr_AL_6.
  align_tape.
  do 14 step. finish_norm.
Qed.

Lemma R1 : forall b a l, const 0 <{{H}} (1 >> [1]^^b *> 0 >> 1 >> [1]^^a *> l) -->+ const 0 <{{H}} (1 >> 1 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^a *> l).
Proof.
  intros.
  start_progress.
  follow cr_DR_1_1.
  execute.
  follow cr_FL_1_1.
  do 5 step. finish_norm.
Qed.

Lemma R2 : forall b y t, const 0 <{{H}} (1 >> [1]^^b *> 0 >> 0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{H}} (1 >> 1 >> 0 >> 1 >> 1 >> [1]^^b *> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_DR_1_1.
  execute.
  follow cr_GL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_DR_1_1.
  execute.
  follow cr_FL_1_1.
  do 6 step. finish_norm.
Qed.

Lemma ENTRY : forall b w, const 0 <{{H}} (1 >> [1]^^b *> 0 >> w) -->+ ([1]^^b *> 1 >> 1 >> const 0) {{D}}> (0 >> w).
Proof.
  intros.
  start_progress.
  follow cr_DR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma LOOP : forall r Y z, (1 >> 1 >> [1]^^r *> 0 >> Y) {{D}}> (0 >> 0 >> z) -->+ ([1]^^r *> 0 >> 1 >> 1 >> 0 >> Y) {{D}}> (0 >> z).
Proof.
  intros.
  start_progress.
  follow cr_GL_1_1.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  rewrite (align_lpow 1 [] _ _). simpl app.
  execute.
  follow cr_DR_1_1.
  do 0 step. finish_norm.
Qed.

Lemma FINAL : forall s m y t, ([1]^^s *> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{D}}> (0 >> 1 >> [1]^^y *> t) -->+ const 0 <{{H}} (1 >> [1;0;1]^^m *> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1]^^s *> 1 >> 0 >> [1]^^y *> t).
Proof.
  intros.
  start_progress.
  follow cr_FL_1_1.
  execute.
  follow cr_FL_011_101.
  do 3 step. finish_norm.
Qed.

(** ** The digit family *)

Fixpoint lft (ds : list nat) : side :=
  match ds with
  | [] => const 0
  | d :: t => 0 >> [1]^^d *> lft t
  end.

(** Kd ds a b = 0^inf <H (1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 ...) : the head is on the blank left of the word *)
Definition Kd (ds : list nat) (a b : nat) : Q * tape :=
  const 0 <{{H}} (1 >> [1]^^b *> 0 >> [1]^^a *> lft ds).

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
  ([1]^^(2 * i + s) *> 0 >> Y) {{D}}> ([0]^^i *> 0 >> z) -->*
  ([1]^^s *> [0;1;1]^^i *> 0 >> Y) {{D}}> (0 >> z).
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

Lemma LOOPS_blank : forall i s,
  ([1]^^(2 * i + s) *> const 0) {{D}}> const 0 -->*
  ([1]^^s *> [0;1;1]^^i *> const 0) {{D}}> const 0.
Proof.
  intros. pose proof (LOOPS i s (const 0) (const 0)) as Hx.
  rewrite zeros_shift, zeros_const, const0 in Hx. exact Hx.
Qed.

(** ** The rebuild R4O3 and halt R4Ex *)

Lemma lpow_double : forall {T} (xs : list T) m, xs^^(2 * m) = (xs ++ xs)^^m.
Proof.
  induction m. - reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia. cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
Qed.

Lemma blocks_even : forall m, [0;1;1]^^(2 * m) *> const 0 = [0;1;1;0;1;1]^^m *> const 0.
Proof. intros. rewrite lpow_double. reflexivity. Qed.

(** trip m = (0,1,2)^m (0,1,1), top digit first *)
Fixpoint trip (m : nat) : list nat :=
  match m with
  | O => [0%nat; 1%nat; 1%nat]
  | S m' => 0%nat :: 1%nat :: 2%nat :: trip m'
  end.

Lemma lft_trip : forall m, lft (trip m) = [0;0;1;0;1;1]^^m *> 0 >> 0 >> 1 >> 0 >> 1 >> const 0.
Proof. induction m. - reflexivity. - simpl. simpl in IHm. rewrite IHm. reflexivity. Qed.

Lemma KR4O3 : forall k m, Kd (repeat 0%nat k) 0 (4 * m + 3) -->+ Kd (2%nat :: trip m) 0 1.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (4 * m + 3 + 2) with (2 * (2 * S m) + 1) by lia.
  follow (LOOPS_blank (2 * S m) 1).
  change ([1]^^1 *> [0;1;1]^^(2 * S m) *> const 0) with (1 >> ([0;1;1]^^(2 * S m) *> const 0)).
  rewrite blocks_even.
  apply progress_evstep.
  eapply progress_evstep_trans; [apply (R4O3 m) |].
  apply evstep_refl'. unfold Kd. simpl lft. rewrite lft_trip. reflexivity.
Qed.

(** Even b: the machine halts in 5 steps after the fill loop (I0 = 1RZ). *)
Definition c_end (m : nat) : state * tape :=
  (1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{I}}> const 0.

Lemma HALT5x : forall m,
  (0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{D}}> const 0 -->* c_end m.
Proof. intros. unfold c_end. do 5 step. apply evstep_refl. Qed.

Lemma c_end_halted : forall m, halted tm (c_end m).
Proof. intros. unfold c_end. simpl. reflexivity. Qed.

Lemma KR4Ex : forall k m, Kd (repeat 0%nat k) 0 (2 * m) -->* c_end m.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  apply progress_evstep.
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (2 * m + 2) with (2 * S m + 0) by lia.
  follow (LOOPS_blank (S m) 0).
  simpl lpow.
  apply HALT5x.
Qed.

Lemma init_reach : c0 -->* Kd [1%nat; 1%nat] 0 1.
Proof. unfold Kd. simpl. do 49 step. finish. Qed.

Local Open Scope nat_scope.

Ltac absmod x k :=
  let q := fresh "q" in let r := fresh "r" in
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x k) as H1;
  assert (H2 : x mod k < k) by (apply Nat.mod_upper_bound; discriminate);
  set (q := x / k) in *; set (r := x mod k) in *; clearbody q r.
Ltac mods :=
  repeat match goal with
  | Hx : context[?x mod ?k] |- _ => absmod x k
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

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

(** ** Iteration *)

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin : forall g, (forall a, a + 1 <= g a) -> forall n x, x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_par : forall g T, (forall y, T <= y -> T <= g y /\ g y mod 2 = (y + 1) mod 2) ->
  forall n x, T <= x -> T <= iter n g x /\ iter n g x mod 2 = (x + n) mod 2.
Proof.
  intros g T Hg. induction n; intros x Hx; cbn [iter].
  - split; [lia | f_equal; lia].
  - destruct (IHn x Hx) as [H1 H2]. destruct (Hg _ H1) as [H3 H4]. split; [exact H3 |].
    rewrite H4. mods; lia.
Qed.

(** ** The exact clearing functions *)

Fixpoint UX (j : nat) : (nat -> nat) * nat :=
  match j with
  | O => (fun x => 3 * x + 7, 7)
  | S i => (fun x => iter (x - 2 * i) (fst (UX i)) (snd (UX i)),
            fst (UX i) (fst (UX i) (snd (UX i))))
  end.

Definition U (j : nat) : nat -> nat := fst (UX j).
Definition X (j : nat) : nat := snd (UX j).

Lemma U_0 : forall x, U 0 x = 3 * x + 7.
Proof. reflexivity. Qed.

Lemma U_S : forall j x, U (S j) x = iter (x - 2 * j) (U j) (X j).
Proof. reflexivity. Qed.

Lemma X_0 : X 0 = 7.
Proof. reflexivity. Qed.

Lemma X_S : forall j, X (S j) = U j (U j (X j)).
Proof. reflexivity. Qed.

Opaque U X.

Lemma growth : forall j, (forall x, x + 2 * j + 5 <= U j x) /\ 4 * j + 7 <= X j.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; lia | rewrite X_0; lia].
  - split.
    + intros x. rewrite U_S.
      pose proof (iter_lin (U j) ltac:(intros a; specialize (Hu a); lia) (x - 2 * j) (X j)). lia.
    + rewrite X_S. pose proof (Hu (X j)). pose proof (Hu (U j (X j))). lia.
Qed.

Lemma Ugrow : forall j x, x + 2 * j + 5 <= U j x.
Proof. intros. apply growth. Qed.

Lemma Xgrow : forall j, 4 * j + 7 <= X j.
Proof. intros. apply growth. Qed.

Lemma U_ge_X : forall i z, X i <= U (S i) z.
Proof.
  intros. rewrite U_S. apply iter_ge. intros a. pose proof (Ugrow i a). lia.
Qed.

Lemma parity : forall j, (forall x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2) /\ X j mod 2 = 1.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; mods; lia | rewrite X_0; reflexivity].
  - assert (Hg : forall y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2).
    { intros y Hy. split; [pose proof (Ugrow j y); lia | auto]. }
    split.
    + intros x Hx'. rewrite U_S. pose proof (Xgrow j).
      destruct (iter_par (U j) (2 * j) Hg (x - 2 * j) (X j) ltac:(lia)) as [_ Hp].
      rewrite Hp. mods; lia.
    + rewrite X_S. pose proof (Xgrow j).
      destruct (Hg (X j)) as [H1 H2]; [lia |]. destruct (Hg (U j (X j)) H1) as [_ H3].
      rewrite H3. mods; lia.
Qed.

Lemma Upar : forall j x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2.
Proof. intros. apply parity. assumption. Qed.

Lemma Ustep : forall j y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2.
Proof. intros. split; [pose proof (Ugrow j y); lia | apply Upar; assumption]. Qed.

(** ** Clearing at the machine level, with exact values *)

Lemma CHx : forall v Us B, Kd (v :: Us) 0 B -->* Kd (0 :: Us) 0 (iter v (U 0) B).
Proof.
  induction v; intros Us B.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2 |].
    follow (R1iter (B + 2) (v :: Us) 1).
    rewrite iter_S', U_0. replace (3 * B + 7) with (1 + 3 * (B + 2)) by lia.
    apply IHv.
Qed.

Definition CDPx (j : nat) : Prop := forall v Us B, 2 * j <= B ->
  Kd (repeat 0 j ++ v :: Us) 0 B -->* Kd (repeat 0 (S j) ++ Us) 0 (iter v (U j) B).

Fixpoint Yb (t n x : nat) : nat :=
  match n with
  | O => x
  | S n' => U (t + n') (U (t + n') (Yb t n' x))
  end.

Lemma Yb_X : forall j, Yb 0 j 7 = X j.
Proof. induction j. - reflexivity. - simpl Yb. rewrite IHj, X_S. reflexivity. Qed.

Lemma Yb_ge : forall t n x, 2 * t <= x -> 2 * (t + n) <= Yb t n x.
Proof.
  intros t n x Hx. destruct n as [| n']. - simpl. lia.
  - simpl Yb. pose proof (Ugrow (t + n') (U (t + n') (Yb t n' x))). lia.
Qed.

Lemma BLKx : forall D, (forall j', j' < D -> CDPx j') ->
  forall n t V x, t + n <= D -> 2 * t <= x ->
  Kd (repeat 0 t ++ repeat 2 n ++ V) 0 x -->* Kd (repeat 0 (t + n) ++ V) 0 (Yb t n x).
Proof.
  intros D HD. induction n as [| n IHn]; intros t V x Hd Hx.
  - replace (t + 0) with t by lia. apply evstep_refl.
  - rewrite <- repeat_snoc.
    follow (IHn t (2 :: V) x ltac:(lia) Hx).
    follow (HD (t + n) ltac:(lia) 2 V (Yb t n x) (Yb_ge t n x Hx)).
    replace (t + S n) with (S (t + n)) by lia. apply evstep_refl.
Qed.

Lemma CDPx_all : forall j, CDPx j.
Proof.
  intro j. induction j as [j IH] using lt_wf_ind.
  destruct j as [| n].
  - intros v Us B _. simpl. apply CHx.
  - intro v. induction v as [| w IHw]; intros Us B HB.
    + rewrite repeat_snoc. apply evstep_refl.
    + remember (B - 2 * S n) as s eqn:Hs.
      assert (HB' : B = 2 * S n + s) by lia.
      assert (Hr : Kd (repeat 0 (S n) ++ S w :: Us) 0 B -->*
                   Kd (repeat 2 n ++ S (S s) :: w :: Us) 0 7).
      { rewrite HB'. eapply evstep_trans; [apply progress_evstep, KR3 |].
        follow (R1iter 2 (repeat 2 n ++ S (S s) :: w :: Us) 1). finish. }
      follow Hr.
      follow (BLKx (S n) IH n 0 (S (S s) :: w :: Us) 7 ltac:(lia) ltac:(lia)).
      rewrite Yb_X.
      follow (IH n ltac:(lia) (S (S s)) (w :: Us) (X n) ltac:(pose proof (Xgrow n); lia)).
      replace (iter (S (S s)) (U n) (X n)) with (U (S n) B)
        by (rewrite U_S; f_equal; lia).
      follow (IHw Us (U (S n) B) ltac:(pose proof (Ugrow (S n) B); lia)).
      rewrite iter_S'. apply evstep_refl.
Qed.

(** ** Residues mod 8: from depth 2 on, one unit sends even b to 7 and odd b to 0 (mod 8) *)

Lemma U1_mod8 : forall n,
  (n mod 4 = 0 -> iter n (U 0) 7 mod 8 = 7) /\ (n mod 4 = 1 -> iter n (U 0) 7 mod 8 = 4) /\
  (n mod 4 = 2 -> iter n (U 0) 7 mod 8 = 3) /\ (n mod 4 = 3 -> iter n (U 0) 7 mod 8 = 0).
Proof.
  induction n.
  - cbn [iter]. repeat split; intros; mods; lia.
  - cbn [iter]. rewrite U_0. destruct IHn as [H0 [H1 [H2 H3]]].
    repeat split; intros; mods; lia.
Qed.

Lemma U1_x : forall x, U 1 x = iter x (U 0) 7.
Proof. intros. rewrite U_S, X_0. f_equal. lia. Qed.

Lemma U1_0 : forall y, y mod 4 = 0 -> U 1 y mod 8 = 7.
Proof. intros y Hy. rewrite U1_x. apply (U1_mod8 y). exact Hy. Qed.

Lemma U1_3 : forall y, y mod 4 = 3 -> U 1 y mod 8 = 0.
Proof. intros y Hy. rewrite U1_x. apply (U1_mod8 y). exact Hy. Qed.

Lemma X1_val : X 1 = 91.
Proof. rewrite X_S, X_0, !U_0. reflexivity. Qed.

Lemma m8_4_0 : forall y, y mod 8 = 0 -> y mod 4 = 0.
Proof. intros; mods; lia. Qed.

Lemma m8_4_3 : forall y, y mod 8 = 7 -> y mod 4 = 3.
Proof. intros; mods; lia. Qed.

Lemma U2_orbit : forall n, (n mod 2 = 1 -> iter n (U 1) 91 mod 8 = 0) /\
  (1 <= n -> n mod 2 = 0 -> iter n (U 1) 91 mod 8 = 7).
Proof.
  induction n as [| n [H1 H2]].
  - split; intros; mods; lia.
  - cbn [iter]. split.
    + intros Hn. destruct n as [| n'].
      * cbn [iter]. apply U1_3. reflexivity.
      * apply U1_3, m8_4_3. apply H2; [lia | mods; lia].
    + intros _ Hn. apply U1_0, m8_4_0. apply H1. mods; lia.
Qed.

Definition Pm8 (j : nat) : Prop :=
  (forall x, 2 * j <= x -> (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0)) /\ X j mod 8 = 7.

Lemma Pm8_2 : Pm8 2.
Proof.
  split.
  - intros x Hx. rewrite U_S, X1_val.
    destruct (U2_orbit (x - 2 * 1)) as [H1 H2].
    split; intros Hp; [apply H2 | apply H1]; mods; lia.
  - rewrite X_S, X1_val. apply U1_0, m8_4_0. apply (proj1 (U2_orbit 1)). reflexivity.
Qed.

Lemma iter_m8 : forall j, (forall x, 2 * j <= x -> (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0)) ->
  forall n x, 2 * j <= x -> x mod 8 = 7 ->
    2 * j <= iter n (U j) x /\ (n mod 2 = 0 -> iter n (U j) x mod 8 = 7) /\ (n mod 2 = 1 -> iter n (U j) x mod 8 = 0).
Proof.
  intros j Hj. induction n as [| n IH]; intros x Hx H7.
  - cbn [iter]. repeat split; intros; [lia | assumption | mods; lia].
  - destruct (IH x Hx H7) as [G1 [G2 G3]]. cbn [iter].
    pose proof (Ugrow j (iter n (U j) x)). destruct (Hj _ G1) as [K0 K1].
    repeat split; [lia | |]; intros Hn.
    + apply K0. assert (Hn' : n mod 2 = 1) by (mods; lia). specialize (G3 Hn'). mods; lia.
    + apply K1. assert (Hn' : n mod 2 = 0) by (mods; lia). specialize (G2 Hn'). mods; lia.
Qed.

Lemma Pm8_S : forall j, 2 <= j -> Pm8 j -> Pm8 (S j).
Proof.
  intros j Hj [Hu Hx]. pose proof (Xgrow j) as HXg.
  split.
  - intros x Hx'. rewrite U_S.
    destruct (iter_m8 j Hu (x - 2 * j) (X j) ltac:(lia) Hx) as [_ [H0 H1]].
    split; intros Hp; [apply H0 | apply H1]; mods; lia.
  - rewrite X_S.
    destruct (iter_m8 j Hu 2 (X j) ltac:(lia) Hx) as [_ [H0 _]]. apply H0. reflexivity.
Qed.

Lemma Pm8_all : forall j, 2 <= j -> Pm8 j.
Proof.
  intros j Hj. induction j as [| j IH]; [lia |].
  destruct (Nat.eq_dec j 1) as [-> | Hne]; [exact Pm8_2 |].
  apply Pm8_S; [lia | apply IH; lia].
Qed.

Lemma U_mod8 : forall j x, 2 <= j -> 2 * j <= x ->
  (x mod 2 = 0 -> U j x mod 8 = 7) /\ (x mod 2 = 1 -> U j x mod 8 = 0).
Proof. intros j x Hj Hx. apply (proj1 (Pm8_all j Hj)). exact Hx. Qed.

(** ** Clearing the rebuilt lists (2 :: trip m) *)

(** clearing the m (0,1,2) triples of trip m from depth j *)
Fixpoint Tpre (m j B : nat) : nat :=
  match m with
  | O => B
  | S m' => Tpre m' (j + 3) (U (j + 2) (U (j + 2) (U (j + 1) B)))
  end.

Definition Tv (m j B : nat) : nat := U (j + 3 * m + 2) (U (j + 3 * m + 1) (Tpre m j B)).

Lemma Tpre_par : forall m j B, 2 * (j + 1) <= B ->
  2 * (j + 3 * m + 1) <= Tpre m j B /\ Tpre m j B mod 2 = (B + m) mod 2.
Proof.
  induction m; intros j B HB.
  - cbn [Tpre]. split; [lia | f_equal; lia].
  - cbn [Tpre].
    pose proof (Ugrow (j + 1) B) as G1.
    pose proof (Ugrow (j + 2) (U (j + 1) B)) as G2.
    pose proof (Ugrow (j + 2) (U (j + 2) (U (j + 1) B))) as G3.
    pose proof (Upar (j + 1) B ltac:(lia)) as P1.
    pose proof (Upar (j + 2) (U (j + 1) B) ltac:(lia)) as P2.
    pose proof (Upar (j + 2) (U (j + 2) (U (j + 1) B)) ltac:(lia)) as P3.
    destruct (IHm (j + 3) (U (j + 2) (U (j + 2) (U (j + 1) B))) ltac:(lia)) as [H3 H4].
    split; [lia |]. rewrite H4. mods; lia.
Qed.

Lemma TRIPS : forall m j B, 2 * (j + 1) <= B ->
  Kd (repeat 0 j ++ trip m) 0 B -->* Kd (repeat 0 (j + 3 * m) ++ [0; 1; 1]) 0 (Tpre m j B).
Proof.
  induction m; intros j B HB.
  - replace (j + 3 * 0) with j by lia. apply evstep_refl.
  - cbn [trip Tpre]. rewrite (repeat_snoc 0 j).
    follow (CDPx_all (S j) 1 (2 :: trip m) B ltac:(lia)).
    change (iter 1 (U (S j)) B) with (U (S j) B).
    pose proof (Ugrow (S j) B) as G1.
    follow (CDPx_all (S (S j)) 2 (trip m) (U (S j) B) ltac:(lia)).
    change (iter 2 (U (S (S j))) (U (S j) B)) with (U (S (S j)) (U (S (S j)) (U (S j) B))).
    pose proof (Ugrow (S (S j)) (U (S j) B)) as G2.
    pose proof (Ugrow (S (S j)) (U (S (S j)) (U (S j) B))) as G3.
    replace (S (S (S j))) with (j + 3) in * by lia.
    replace (S (S j)) with (j + 2) in * by lia.
    replace (S j) with (j + 1) in * by lia.
    follow (IHm (j + 3) (U (j + 2) (U (j + 2) (U (j + 1) B))) ltac:(lia)).
    replace (j + 3 + 3 * m) with (j + 3 * S m) by lia. apply evstep_refl.
Qed.

Lemma TRIP_ALL : forall m j B, 2 * (j + 1) <= B ->
  Kd (repeat 0 j ++ trip m) 0 B -->* Kd (repeat 0 (j + 3 * m + 3)) 0 (Tv m j B).
Proof.
  intros m j B HB.
  follow (TRIPS m j B HB).
  destruct (Tpre_par m j B HB) as [H1 _].
  rewrite (repeat_snoc 0 (j + 3 * m)).
  follow (CDPx_all (S (j + 3 * m)) 1 [1] (Tpre m j B) ltac:(lia)).
  change (iter 1 (U (S (j + 3 * m))) (Tpre m j B)) with (U (S (j + 3 * m)) (Tpre m j B)).
  pose proof (Ugrow (S (j + 3 * m)) (Tpre m j B)) as G1.
  follow (CDPx_all (S (S (j + 3 * m))) 1 [] (U (S (j + 3 * m)) (Tpre m j B)) ltac:(lia)).
  rewrite app_nil_r. unfold Tv. cbn [iter].
  replace (S (S (S (j + 3 * m)))) with (j + 3 * m + 3) by lia.
  replace (S (S (j + 3 * m))) with (j + 3 * m + 2) by lia.
  replace (S (j + 3 * m)) with (j + 3 * m + 1) by lia.
  apply evstep_refl.
Qed.

Lemma Tv_par : forall m j B, 2 * (j + 1) <= B -> Tv m j B mod 2 = (B + m) mod 2.
Proof.
  intros m j B HB. destruct (Tpre_par m j B HB) as [H1 H2]. unfold Tv.
  set (D1 := j + 3 * m + 1) in *. set (D2 := j + 3 * m + 2) in *. set (z := Tpre m j B) in *.
  pose proof (Ugrow D1 z).
  pose proof (Upar D1 z ltac:(lia)) as P1. pose proof (Upar D2 (U D1 z) ltac:(lia)) as P2.
  mods; lia.
Qed.

(** When B + m is odd (so z before the last two 1-digits is odd) and j >= 1, the first 1 sends z to 0 mod 8
    and the second 1 sends that even number to 7 mod 8. *)
Lemma Tv_mod8 : forall m j B, 1 <= j -> 2 * (j + 1) <= B -> (B + m) mod 2 = 1 -> Tv m j B mod 8 = 7.
Proof.
  intros m j B Hj HB Hp. destruct (Tpre_par m j B HB) as [H1 H2]. unfold Tv.
  set (D1 := j + 3 * m + 1) in *. set (D2 := j + 3 * m + 2) in *. set (z := Tpre m j B) in *.
  assert (Hz : z mod 2 = 1) by (rewrite H2; exact Hp).
  pose proof (Ugrow D1 z).
  destruct (U_mod8 D1 z ltac:(lia) ltac:(lia)) as [_ Z1]. specialize (Z1 Hz).
  destruct (U_mod8 D2 (U D1 z) ltac:(lia) ltac:(lia)) as [Z0 _]. apply Z0. mods; lia.
Qed.

(** ** The 3-cascade run *)

Definition b1 : nat := U 1 10.
Definition second (b : nat) : nat := Tv (b / 4) 1 37.
Definition b2 : nat := second b1.
Definition b3 : nat := second b2.

Lemma b1_def : b1 = U 1 10.
Proof. reflexivity. Qed.

Lemma b2_def : b2 = second b1.
Proof. reflexivity. Qed.

Lemma b3_def : b3 = second b2.
Proof. reflexivity. Qed.

Opaque b1 b2 b3 Tv.

Lemma b1_mod8 : b1 mod 8 = 3.
Proof. rewrite b1_def, U1_x. apply (proj1 (proj2 (proj2 (U1_mod8 10)))). reflexivity. Qed.

Lemma div8_3 : forall x, x mod 8 = 3 -> x = 4 * (x / 4) + 3 /\ (x / 4) mod 2 = 0.
Proof. intros x Hx. pose proof (Nat.div_mod_eq x 4). mods; lia. Qed.

Lemma div8_7 : forall x, x mod 8 = 7 -> x = 4 * (x / 4) + 3 /\ (x / 4) mod 2 = 1.
Proof. intros x Hx. pose proof (Nat.div_mod_eq x 4). mods; lia. Qed.

Lemma second_mod8_7 : forall b, b mod 8 = 3 -> second b mod 8 = 7.
Proof.
  intros b Hb. unfold second. destruct (div8_3 b Hb) as [_ Hq].
  apply Tv_mod8; [lia | lia |]. set (q := b / 4) in *. mods; lia.
Qed.

Lemma second_even : forall b, b mod 8 = 7 -> second b mod 2 = 0.
Proof.
  intros b Hb. unfold second. destruct (div8_7 b Hb) as [_ Hq].
  rewrite Tv_par; [| lia]. set (q := b / 4) in *. mods; lia.
Qed.

Lemma b2_mod8 : b2 mod 8 = 7.
Proof. rewrite b2_def. apply second_mod8_7, b1_mod8. Qed.

Lemma b3_even : b3 mod 2 = 0.
Proof. rewrite b3_def. apply second_even, b2_mod8. Qed.

Lemma even_half : forall x, x mod 2 = 0 -> x = 2 * (x / 2).
Proof. intros; mods; lia. Qed.

(** clearing a rebuilt list (2 :: trip m) from Kd _ 0 1 *)
Lemma clear_rebuilt : forall m, Kd (2%nat :: trip m) 0 1 -->* Kd (repeat 0 (1 + 3 * m + 3)) 0 (Tv m 1 37).
Proof.
  intros m.
  change (Kd (2%nat :: trip m) 0 1) with (Kd (repeat 0 0 ++ 2%nat :: trip m) 0 1).
  follow (CDPx_all 0 2 (trip m) 1 ltac:(lia)).
  change (iter 2 (U 0) 1) with (U 0 (U 0 1)). rewrite !U_0. change (3 * (3 * 1 + 7) + 7) with 37.
  apply (TRIP_ALL m 1 37 ltac:(lia)).
Qed.

Lemma run1 : c0 -->* Kd (repeat 0 2) 0 b1.
Proof.
  follow init_reach.
  change (Kd [1%nat; 1%nat] 0 1) with (Kd (repeat 0 0 ++ 1%nat :: [1%nat]) 0 1).
  follow (CDPx_all 0 1 [1%nat] 1 ltac:(lia)).
  change (iter 1 (U 0) 1) with (U 0 1). rewrite U_0. change (3 * 1 + 7) with 10.
  follow (CDPx_all 1 1 [] 10 ltac:(lia)).
  rewrite app_nil_r. change (iter 1 (U 1) 10) with (U 1 10). rewrite <- b1_def.
  apply evstep_refl.
Qed.

Lemma step_cascade : forall k b, (b mod 8 = 3 \/ b mod 8 = 7) ->
  Kd (repeat 0 k) 0 b -->* Kd (repeat 0 (1 + 3 * (b / 4) + 3)) 0 (second b).
Proof.
  intros k b Hb.
  assert (Hq : b = 4 * (b / 4) + 3).
  { destruct Hb as [H3 | H7]; [destruct (div8_3 b H3) | destruct (div8_7 b H7)]; assumption. }
  rewrite Hq at 1.
  eapply evstep_trans; [apply progress_evstep, (KR4O3 k (b / 4)) |].
  apply clear_rebuilt.
Qed.

Lemma run3 : c0 -->* c_end (b3 / 2).
Proof.
  follow run1.
  follow (step_cascade 2 b1 (or_introl b1_mod8)).
  rewrite <- b2_def.
  follow (step_cascade (1 + 3 * (b1 / 4) + 3) b2 (or_intror b2_mod8)).
  rewrite <- b3_def.
  rewrite (even_half b3 b3_even) at 1.
  apply KR4Ex.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run3) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.
