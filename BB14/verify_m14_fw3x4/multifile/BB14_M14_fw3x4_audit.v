(** Statement check for Neon's BB14_M14_fw3x4.v, from the independent audit (2026-11-23), written without
    looking at the entry and comparison files of this directory.
    Everything the headline statements below mention is either BusyCoq's own definition
    (TM, step/evstep, halted, halts, c0 = A;; blank tape, from BusyCoq.TM instantiated by BB142)
    or defined in THIS file: the two transition tables (transcribed by hand from the machine
    strings: M14_fw3x4's TNF string, and M14_fw3's name as published in BB14/), the count of ones, and
    the fast-growing hierarchy (with Coq's Nat.iter).
    The proofs use Neon's file only as a black box: its theorems are rewritten into these terms. *)

From BB8 Require Import Individual142.
From BB8 Require BB14_M14_fw3x4.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Module Neo := BB14_M14_fw3x4.

(** ** 1. The machine strings, transcribed by hand *)

(* New machine, TNF (start A), from the string
   1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN *)
Definition my_new : TM := fun qs =>
  match qs with
  | (A, S0) => Some (S1, TM.R, B) | (A, S1) => Some (S0, TM.L, K)
  | (B, S0) => Some (S1, TM.R, C) | (B, S1) => Some (S1, TM.R, B)
  | (C, S0) => Some (S1, TM.R, D) | (C, S1) => Some (S1, TM.R, M)
  | (D, S0) => Some (S1, TM.R, E) | (D, S1) => Some (S0, TM.L, H)
  | (E, S0) => Some (S1, TM.L, F) | (E, S1) => Some (S1, TM.R, I)
  | (F, S0) => Some (S0, TM.L, A) | (F, S1) => Some (S1, TM.L, G)
  | (G, S0) => Some (S1, TM.R, L) | (G, S1) => Some (S0, TM.L, F)
  | (H, S0) => Some (S1, TM.L, K) | (H, S1) => Some (S1, TM.L, D)
  | (I, S0) => Some (S1, TM.R, J) | (I, S1) => Some (S0, TM.R, B)
  | (J, S0) => Some (S1, TM.R, G) | (J, S1) => Some (S0, TM.L, K)
  | (K, S0) => Some (S1, TM.L, A) | (K, S1) => Some (S1, TM.L, K)
  | (L, S0) => None                | (L, S1) => Some (S0, TM.L, F)
  | (M, S0) => Some (S0, TM.L, N) | (M, S1) => Some (S1, TM.L, A)
  | (N, S0) => Some (S0, TM.R, E) | (N, S1) => Some (S1, TM.L, N)
  end.

(* Current BB(14) entry M14_fw3, exactly as named in the busy-beaver repo (start A, halt 1RZ = undefined here):
   1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_1LN1LK_1RK0LH_1LD0RK *)
Definition my_old : TM := fun qs =>
  match qs with
  | (A, S0) => Some (S1, TM.R, B) | (A, S1) => Some (S1, TM.R, A)
  | (B, S0) => Some (S1, TM.R, I) | (B, S1) => Some (S1, TM.R, C)
  | (C, S0) => Some (S0, TM.L, D) | (C, S1) => Some (S1, TM.L, G)
  | (D, S0) => Some (S0, TM.R, E) | (D, S1) => Some (S1, TM.L, D)
  | (E, S0) => Some (S0, TM.L, K) | (E, S1) => Some (S1, TM.R, F)
  | (F, S0) => Some (S1, TM.R, M) | (F, S1) => Some (S0, TM.R, A)
  | (G, S0) => Some (S1, TM.R, A) | (G, S1) => Some (S0, TM.L, H)
  | (H, S0) => Some (S1, TM.L, G) | (H, S1) => Some (S1, TM.L, H)
  | (I, S0) => Some (S1, TM.R, E) | (I, S1) => Some (S0, TM.L, J)
  | (J, S0) => Some (S1, TM.L, H) | (J, S1) => Some (S1, TM.L, I)
  | (K, S0) => None                | (K, S1) => Some (S0, TM.L, L)
  | (L, S0) => Some (S1, TM.L, N) | (L, S1) => Some (S1, TM.L, K)
  | (M, S0) => Some (S1, TM.R, K) | (M, S1) => Some (S0, TM.L, H)
  | (N, S0) => Some (S1, TM.L, D) | (N, S1) => Some (S0, TM.R, K)
  end.

Local Open Scope nat_scope.

(** ** 2. A count of ones and the fast-growing hierarchy, defined here *)

Definition is1 (x : Sym) : bool := match x with S1 => true | S0 => false end.

(* [my_ones c n]: the tape of [c] is a finite word padded with blanks on both sides and holds n ones. *)
Definition my_ones (c : Q * tape) (n : nat) : Prop :=
  exists q l s r, c = (q, (l *> const S0, s, r *> const S0)) /\
                  n = length (filter is1 (rev l ++ s :: r)).

Fixpoint fgh (k : nat) : nat -> nat :=            (* f_0 = S, f_(k+1)(n) = f_k^n(n) *)
  match k with
  | O => S
  | S k' => fun n => Nat.iter n (fgh k') n
  end.
Definition fw (n : nat) : nat := fgh n n.        (* f_omega(n) = f_n(n) *)
Fixpoint fwk (k : nat) : nat -> nat :=          (* f_(omega+k): f_(omega+k+1)(n) = f_(omega+k)^n(n) *)
  match k with
  | O => fw
  | S k' => fun n => Nat.iter n (fwk k') n
  end.

(** ** 3. Bridges to the definitions of Neon's file *)

Lemma ext_step : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c c', c -[ t1 ]-> c' -> c -[ t2 ]-> c'.
Proof.
  intros t1 t2 E c c' H. destruct H as [q q' s s' l r Ht | q q' s s' l r Ht].
  - apply step_left. rewrite <- E. exact Ht.
  - apply step_right. rewrite <- E. exact Ht.
Qed.

Lemma ext_evstep : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c c', c -[ t1 ]->* c' -> c -[ t2 ]->* c'.
Proof.
  intros t1 t2 E c c' H. induction H as [c | c c1 c2 H1 _ IH].
  - apply evstep_refl.
  - eapply evstep_step; [eapply ext_step; [exact E | exact H1] | exact IH].
Qed.

Lemma ext_multistep : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall n c c', c -[ t1 ]->> n / c' -> c -[ t2 ]->> n / c'.
Proof.
  intros t1 t2 E n c c' H. induction H as [c | n c c1 c2 H1 _ IH].
  - apply multistep_0.
  - eapply multistep_S; [eapply ext_step; [exact E | exact H1] | exact IH].
Qed.

Lemma ext_halted : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c, halted t1 c -> halted t2 c.
Proof.
  intros t1 t2 E [q [[l s] r]] H. unfold halted in *. rewrite <- E. exact H.
Qed.

Lemma new_eq : forall q s, my_new (q, s) = Neo.tm_tnf (q, s).
Proof. intros [] []; reflexivity. Qed.

Lemma old_eq : forall q s, my_old (q, s) = Neo.tm_M14_fw3 (q, s).
Proof. intros [] []; reflexivity. Qed.

Lemma count_eq : forall xs, Neo.count1 xs = length (filter is1 xs).
Proof. induction xs as [| [] xs IH]; cbn; [reflexivity | exact IH | rewrite IH; reflexivity]. Qed.

Lemma count_app : forall xs ys, length (filter is1 (xs ++ ys)) = length (filter is1 xs) + length (filter is1 ys).
Proof. intros. rewrite filter_app, length_app. reflexivity. Qed.

Lemma count_rev : forall xs, length (filter is1 (rev xs)) = length (filter is1 xs).
Proof.
  induction xs as [| x xs IH]; cbn; [reflexivity |].
  rewrite count_app, IH. destruct x; cbn; lia.
Qed.

Lemma ones_iff : forall c n, Neo.ones c n <-> my_ones c n.
Proof.
  intros c n. split.
  - intros [q [l [r [s [Hc Hn]]]]]. exists q, l, s, r. split; [exact Hc |].
    rewrite count_app, count_rev, Hn, !count_eq. destruct s; cbn [filter is1 length Neo.sym_val]; lia.
  - intros [q [l [s [r [Hc Hn]]]]]. exists q, l, r, s. split; [exact Hc |].
    rewrite Hn, count_app, count_rev, !count_eq. destruct s; cbn [filter is1 length Neo.sym_val]; lia.
Qed.

Transparent Neo.f Neo.f_omega Neo.f_omega1 Neo.f_omega2 Neo.f_omega3.

Lemma iter_eq : forall {X} n (g : X -> X) x, Nat.iter n g x = Neo.iter n g x.
Proof.
  induction n; intros; [reflexivity |].
  change (g (Nat.iter n g x) = g (Neo.iter n g x)). rewrite IHn. reflexivity.
Qed.

Lemma iter_ext : forall {X} (g h : X -> X), (forall x, g x = h x) -> forall n x, Neo.iter n g x = Neo.iter n h x.
Proof. intros X g h E n. induction n; intros x; cbn; [reflexivity | rewrite IHn, E; reflexivity]. Qed.

Lemma fgh_eq : forall k n, fgh k n = Neo.f k n.
Proof.
  induction k as [| k IH]; intros n; cbn; [reflexivity |].
  rewrite iter_eq. apply iter_ext. exact IH.
Qed.

Lemma Fw_eq : forall n, fw n = Neo.f_omega n.
Proof. intros n. unfold fw, Neo.f_omega. apply fgh_eq. Qed.

Lemma Fw3_eq : forall n, fwk 3 n = Neo.f_omega3 n.
Proof.
  intros n. cbn [fwk]. unfold Neo.f_omega3, Neo.f_omega2, Neo.f_omega1.
  rewrite iter_eq. apply iter_ext. intros x.
  rewrite iter_eq. apply iter_ext. intros y.
  rewrite iter_eq. apply iter_ext. intros w.
  apply Fw_eq.
Qed.

Lemma bound_eq : Nat.iter 4 (fwk 3) (fw 4) = Neo.iter 4 Neo.f_omega3 (Neo.f_omega 4).
Proof. rewrite iter_eq, Fw_eq. apply iter_ext. exact Fw3_eq. Qed.

(** ** 4. Headline statements in these terms *)

(* The new machine halts from the blank tape (start A). *)
Theorem my_new_halts : halts my_new c0.
Proof.
  destruct Neo.halt_tnf as [n [ch [Hrun Hh]]].
  exists n, ch. split.
  - eapply ext_multistep; [| exact Hrun]. intros q s. symmetry. apply new_eq.
  - eapply ext_halted; [| exact Hh]. intros q s. symmetry. apply new_eq.
Qed.

(* EVERY halting configuration reached from the blank tape holds more than f_(omega+3)^4(f_omega(4)) ones
   (and one exists).  Stated universally so that it does not rely on picking a particular run. *)
Theorem my_new_sigma :
  (exists c n, c0 -[ my_new ]->* c /\ halted my_new c /\ my_ones c n) /\
  (forall c n, c0 -[ my_new ]->* c -> halted my_new c -> my_ones c n ->
     Nat.iter 4 (fwk 3) (fw 4) < n).
Proof.
  assert (E : forall q s, Neo.tm_tnf (q, s) = my_new (q, s)) by (intros; symmetry; apply new_eq).
  assert (E' : forall q s, my_new (q, s) = Neo.tm_tnf (q, s)) by apply new_eq.
  destruct Neo.sigma_bound_tnf as [c0' [n0 [Hrun0 [Hh0 [Ho0 Hgt]]]]].
  split.
  - exists c0', n0. split; [eapply ext_evstep; eauto |]. split; [eapply ext_halted; eauto |].
    apply ones_iff. exact Ho0.
  - intros c n Hrun Hh Ho.
    apply (ext_evstep _ _ E') in Hrun. apply (ext_halted _ _ E') in Hh. apply ones_iff in Ho.
    assert (c = c0') by exact (Neo.evstep_halted_unique _ _ _ _ Hrun Hh Hrun0 Hh0). subst c.
    assert (n = n0) by exact (Neo.ones_unique _ _ _ Ho Ho0). subst n.
    rewrite bound_eq. exact Hgt.
Qed.

(* M14_fw3 (the current BB(14) entry, as named in the repo) halts, and EVERY halting configuration of it
   holds fewer ones than EVERY halting configuration of the new machine. *)
Definition my_perm_old (q : Q) : Q :=
  match q with
  (* first-visit order of my_old from A on the blank tape: A B I E K L N D F C J M H G (../../tools/m14_fw3x4_lit_chk.py) *)
  | A => A | B => B | C => J | D => H | E => D | F => I | G => N
  | H => M | I => C | J => K | K => E | L => F | M => L | N => G
  end.

Lemma my_perm_old_ok : Perm my_old Neo.tm_M14_fw3_tnf my_perm_old.
Proof.
  split.
  - intros [] [] Hn; cbn in Hn |- *; congruence.
  - intros [] [] s' d q' Hs; cbn in Hs |- *; inversion Hs; subst; reflexivity.
Qed.

Theorem my_beats :
  halts my_old c0 /\
  (forall c1 n1 c2 n2,
     c0 -[ my_old ]->* c1 -> halted my_old c1 -> my_ones c1 n1 ->
     c0 -[ my_new ]->* c2 -> halted my_new c2 -> my_ones c2 n2 ->
     n1 < n2).
Proof.
  assert (Eo : forall q s, my_old (q, s) = Neo.tm_M14_fw3 (q, s)) by apply old_eq.
  assert (En : forall q s, my_new (q, s) = Neo.tm_tnf (q, s)) by apply new_eq.
  destruct Neo.beats_M14_fw3_exact as [[co [no [cn [nn [Hro [Hho [Hoo [Hrn [Hhn [Hon Hlt]]]]]]]]]] Huniv].
  split.
  - (* old halts: its tnf form halts with config co; the old core run gives halting via Neo.M14_Old *)
    destruct Neo.M14_Old.score_exact_old as [c [Hrun [Hh _]]].
    destruct (with_counter Hrun) as [k Hk].
    exists k, c. split.
    + eapply ext_multistep; [| exact Hk]. intros q s. symmetry. apply old_eq.
    + eapply ext_halted; [| exact Hh]. intros q s. symmetry. apply old_eq.
  - intros c1 n1 c2 n2 Hr1 Hh1 Ho1 Hr2 Hh2 Ho2.
    apply (ext_evstep _ _ Eo) in Hr1. apply (ext_halted _ _ Eo) in Hh1. apply ones_iff in Ho1.
    apply (ext_evstep _ _ En) in Hr2. apply (ext_halted _ _ En) in Hh2. apply ones_iff in Ho2.
    (* move the old run to the TNF table by the renaming above (this file's, not Neon's perm_f_old) *)
    assert (HP : Perm Neo.tm_M14_fw3 Neo.tm_M14_fw3_tnf my_perm_old).
    { destruct my_perm_old_ok as [P1 P2]. split.
      - intros q s H. apply P1. rewrite Eo. exact H.
      - intros q s s' d q' H. apply P2. rewrite Eo. exact H. }
    destruct c1 as [q1 t1].
    pose proof (Neo.perm_evstep _ _ _ HP c0 (q1, t1) Hr1) as Hr1'. cbn [fst snd] in Hr1'.
    pose proof (perm_halted _ _ _ q1 t1 HP Hh1) as Hh1'.
    assert (Ho1' : Neo.ones (my_perm_old q1, t1) n1).
    { destruct Ho1 as [q' [L' [R' [s' [Heq Hn]]]]]. inversion Heq; subst.
      exists (my_perm_old q'), L', R', s'. auto. }
    pose proof (Huniv _ _ Hr1' Hh1' Ho1') as Hlt1.
    assert (c2 = cn) by exact (Neo.evstep_halted_unique _ _ _ _ Hr2 Hh2 Hrn Hhn). subst c2.
    assert (n2 = nn) by exact (Neo.ones_unique _ _ _ Ho2 Hon). subst n2.
    (* nn is N_final: the file's N_final is the score of tm_tnf, and ones is unique *)
    destruct Neo.score_exact_tnf as [cf [Hrf [Hhf Hof]]].
    assert (cn = cf) by exact (Neo.evstep_halted_unique _ _ _ _ Hrn Hhn Hrf Hhf). subst cf.
    assert (nn = Neo.N_final) by exact (Neo.ones_unique _ _ _ Hon Hof). subst nn.
    exact Hlt1.
Qed.

(* Both machines halt reading a blank, so for both sigma = (ones at the halt) + 1 under the
   "halting transition writes a 1" convention; the comparison of ones is therefore the comparison of sigma. *)
Lemma my_new_halts_on_blank : forall c, halted my_new c -> exists l r, c = (L, (l, S0, r)).
Proof. intros [q [[l s] r]] H; destruct q, s; cbn in H; try discriminate; eauto. Qed.

Lemma my_old_halts_on_blank : forall c, halted my_old c -> exists l r, c = (K, (l, S0, r)).
Proof. intros [q [[l s] r]] H; destruct q, s; cbn in H; try discriminate; eauto. Qed.

(** ** 5. What the statements depend on *)
Print TM.
Print halts.
Print halts_in.
Print halted.
Print c0.
Print tape0.
Print q0.
Print my_ones.
Print fgh. Print fw. Print fwk.
Print Assumptions my_new_halts.
Print Assumptions my_new_sigma.
Print Assumptions my_beats.
Print Assumptions my_new_halts_on_blank.
Print Assumptions my_old_halts_on_blank.
