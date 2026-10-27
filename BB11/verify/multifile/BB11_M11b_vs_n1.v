(** * The 11-state machine M11b beats n1, the BB(10) entry *)

(** Theorem M11_beats_n1 (no axioms): M11b's halting tape holds Nm ones with f_(omega+1)(f_omega(f_omega 5)) < Nm,
    while n1's halting tape holds Nn ones with Nn + 1 < f_(omega+1)(f_omega 44) (from n1's upper bound
    [BB10_n1_fgh.fgh_level]).  n1 halts on J0 = 1RZ, so its score is Nn + 1; M11b halts on F0 reading 0, so its
    score is Nm + 1.  The n1 files are byte-identical to ../../../BB10/verify/multifile/. *)

From BB8 Require Import Individual112.
From BB8 Require Import BB11_M11b BB11_M11b_fgh.
From BB8 Require Individual102 BB10_n1 BB10_n1_bound BB10_n1_exact BB10_n1_fgh.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Module TM10 := Individual102.Individual102.Permute.Flip.Compute.TM.

(** ** Bridging to BB10_n1_fgh *)

(* Iterating pointwise-equal functions gives equal results. *)
Lemma iter_ext : forall n (g h : nat -> nat) x, (forall y, g y = h y) -> iter n g x = iter n h x.
Proof. induction n; intros g h x Hgh; simpl; [reflexivity |]. rewrite (IHn g h x Hgh), Hgh. reflexivity. Qed.

Lemma iter_n1_agree : forall n (g : nat -> nat) x,
  BB10_n1.iter n g x = iter n g x.
Proof.
  induction n as [| n IH]; intros g x; [reflexivity |].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma fgh_n1_agree : forall k n, BB10_n1_fgh.fgh k n = f k n.
Proof.
  Transparent BB10_n1_fgh.fgh f.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite BB10_n1_fgh.fgh_S, iter_n1_agree, f_S.
  apply iter_ext. exact IH.
Qed.

Lemma f_omega_n1_agree : forall n, BB10_n1_fgh.f_omega n = f_omega n.
Proof.
  intros n. unfold BB10_n1_fgh.f_omega.
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  apply fgh_n1_agree.
Qed.

Lemma f_omega1_n1_agree : forall n, BB10_n1_fgh.f_omega1 n = f_omega1 n.
Proof.
  intros n. rewrite BB10_n1_fgh.f_omega1_iter, iter_n1_agree.
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  apply iter_ext. exact f_omega_n1_agree.
Qed.

Opaque f f_omega f_omega1.

Lemma six_T_le_f_omega_44 : 6 * BB10_n1.arrow 37 2 3 <= f_omega 44.
Proof.
  pose proof (BB10_n1_fgh.arrow_fo 37 3 ltac:(lia)) as H1.
  change (37 + 3 + 1) with 41 in H1.
  pose proof (BB10_n1_fgh.fo_dbl 41 ltac:(lia)) as D41.
  pose proof (BB10_n1_fgh.fo_dbl 42 ltac:(lia)) as D42.
  pose proof (BB10_n1_fgh.fo_dbl 43 ltac:(lia)) as D43.
  rewrite !f_omega_n1_agree in H1; rewrite !f_omega_n1_agree in D41; rewrite !f_omega_n1_agree in D42; rewrite !f_omega_n1_agree in D43.
  lia.
Qed.

(* f_(omega+1) strictly increases from u to S u.  Proved for a variable u, so no closed tower is ever reduced. *)
Lemma f_omega1_S_lt : forall u, 1 <= u -> f_omega1 u < f_omega1 (S u).
Proof.
  intros u Hu.
  Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  change (iter (S u) f_omega (S u)) with (f_omega (iter u f_omega (S u))).
  pose proof (iter_mono_x f_omega f_omega_mono u u (S u) ltac:(lia)).
  pose proof (iter_ge f_omega f_omega_id u (S u)).
  pose proof (f_omega_dbl (iter u f_omega (S u)) ltac:(lia)).
  lia.
Qed.

Lemma f_omega1_44_lt_m11 : f_omega1 (f_omega 44) < f_omega1 (f_omega (f_omega 5)).
Proof.
  pose proof f_omega_5_ge_160 as Hf5.
  assert (Hlt : 44 < f_omega 5) by lia.
  assert (H45 : 2 * f_omega 44 <= f_omega 45).
  { pose proof (BB10_n1_fgh.fo_dbl 44 ltac:(lia)) as D44.
    rewrite !f_omega_n1_agree in D44. exact D44. }
  pose proof (f_omega_id 44) as Hid44.
  assert (Hle45 : f_omega 45 <= f_omega (f_omega 5)) by (apply f_omega_mono; lia).
  assert (H1 : S (f_omega 44) <= f_omega (f_omega 5)) by lia.
  pose proof (f_omega1_mono (S (f_omega 44)) (f_omega (f_omega 5)) H1) as H2.
  assert (H3 : f_omega1 (f_omega 44) < f_omega1 (S (f_omega 44))).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    set (x := f_omega 44) in *.
    assert (Hx : 1 <= x) by lia.
    change (iter (S x) f_omega (S x)) with (f_omega (iter x f_omega (S x))).
    pose proof (iter_mono_x f_omega f_omega_mono x x (S x) ltac:(lia)) as Hm.
    pose proof (iter_ge f_omega f_omega_id x (S x)) as Hge.
    pose proof (f_omega_dbl (iter x f_omega (S x)) ltac:(lia)) as Hdbl.
    lia. }
  lia.
Qed.

Theorem M11_beats_n1 :
  exists cm Nm cn Nn,
    c0 -->* cm /\ halted tm cm /\ ones cm Nm /\
    TM10.evstep BB10_n1.tm TM10.c0 cn /\ TM10.halted BB10_n1.tm cn /\ BB10_n1_bound.ones cn Nn /\
    Nn + 1 < f_omega1 (f_omega 44) /\ f_omega1 (f_omega (f_omega 5)) < Nm /\ Nn + 1 < Nm + 1.
Proof.
  destruct sigma_lower_bound_m11 as [cm [Nm [Hm1 [Hm2 [Hm3 Hm4]]]]].
  destruct BB10_n1_fgh.fgh_level as [cn [Nn [Hn1 [Hn2 [Hn3 [_ Hn_up]]]]]].
  rewrite f_omega1_n1_agree in Hn_up.
  exists cm, Nm, cn, Nn.
  split; [exact Hm1 | split; [exact Hm2 | split; [exact Hm3 |]]].
  split; [exact Hn1 | split; [exact Hn2 | split; [exact Hn3 |]]].
  pose proof six_T_le_f_omega_44 as HT.
  pose proof (f_omega1_mono _ _ HT) as Hup44.
  pose proof f_omega1_44_lt_m11 as Hlt.
  assert (Hstep : f_omega1 (6 * BB10_n1.arrow 37 2 3) < f_omega1 (f_omega 44)).
  { pose proof (BB10_n1_fgh.arrow_fo 37 3 ltac:(lia)) as H1.
    change (37 + 3 + 1) with 41 in H1.
    pose proof (BB10_n1_fgh.fo_dbl 41 ltac:(lia)) as D41.
    pose proof (BB10_n1_fgh.fo_dbl 42 ltac:(lia)) as D42.
    pose proof (BB10_n1_fgh.fo_dbl 43 ltac:(lia)) as D43.
    rewrite !f_omega_n1_agree in H1; rewrite !f_omega_n1_agree in D41; rewrite !f_omega_n1_agree in D42; rewrite !f_omega_n1_agree in D43.
    pose proof (f_omega_id 41) as Hid41.
    assert (Hstrict : S (6 * BB10_n1.arrow 37 2 3) <= f_omega 44) by lia.
    pose proof (f_omega1_mono _ _ Hstrict) as Hmono.
    set (u := 6 * BB10_n1.arrow 37 2 3) in *.
    assert (Hu : 1 <= u) by (unfold u; pose proof (BB10_n1.arrow_ge4 37 3 ltac:(lia)); lia).
    pose proof (f_omega1_S_lt u Hu) as H3.
    lia. }
  split; [lia | split; [exact Hm4 | lia]].
Qed.

Print Assumptions M11_beats_n1.
