(** * BB11_C4_vs_M12 (written as BB11_C4_cmp.v): C4 (11 states) halts with more ones than M12 (12 states, exact score) *)

(** M12 (BB12_M12.v, BB12_M12_bound.v, unchanged) proves
      BB12_M12_bound.score_exact :
        exists c, c0 -[ BB12_M12.tm ]->* c /\ halted BB12_M12.tm c /\ ones c (fst pb2 + snd pb2 / 2 + 3)
    for the explicit pair pb2 of its run.  This file proves an UPPER bound for that number,
      fst pb2 + snd pb2 / 2 + 3 <= f_omega2 (4 * iter 6 f_omega1 12) + 3,
    from the definitions of M12's maps (W, Kc, Kc_full, Kd_step, Kd_iter, D_reload; the argument and most lemmas
    are those of BB13_M13_19_cmp.v for M13b, whose maps are the same), and compares it with C4's lower bound
    4 * f_omega2 (f_omega2 (W 5 (W 2 4) / 4)) + 8 <= fst nFIN (BB11_C4_bound.FIN_dom):
      Theorem beats_M12_exact :
        exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ fst BB12_M12.pb2 + snd BB12_M12.pb2 / 2 + 3 < n.
      Theorem beats_M12_score : exists NM, (M12 halts with NM ones) /\ (C4 halts with n ones, NM < n).
    Both machines halt reading a 0 (C4 in K0, M12 in K0), so sigma = ones + 1 for both if the halting transition
    is completed as 1RZ: the comparison of sigma is the same.
    The fast-growing functions are BB11_C4_bound's (standard).  No closed tower is ever evaluated: every bound is
    proved for variables and instantiated. *)

From BB8 Require Import Individual112.
From BB8 Require Import BB11_C4 BB11_C4_bound.
From BB8 Require BB12_M12 BB12_M12_bound.
From Coq Require Import Lia PeanoNat.

Local Open Scope nat_scope.

Ltac add_div_facts :=
  repeat match goal with
  | |- context [?x / ?k] =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  | H : context [?x / ?k] |- _ =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  end.
Ltac dlia := add_div_facts; lia.

Transparent f_omega f_omega1 f_omega2.
Lemma cmp_Fw_unf : forall n, f_omega n = f n n. Proof. reflexivity. Qed.
Lemma cmp_F1_unf : forall n, f_omega1 n = iter n f_omega n. Proof. reflexivity. Qed.
Lemma cmp_F2_unf : forall n, f_omega2 n = iter n f_omega1 n. Proof. reflexivity. Qed.
Opaque f f_omega f_omega1 f_omega2 W Zs Rnd.

(** The two files define [iter] with the same text. *)
Lemma cmp_iter_M : forall (X : Type) n (g : X -> X) x, BB12_M12.iter n g x = iter n g x.
Proof.
  intros X n g x. induction n as [| n IH]; cbn [BB12_M12.iter iter]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(** ** Generic facts (BB13_M13_19_cmp.v) *)

Lemma cmp_iter_diag : forall g, (forall a b, a <= b -> g a <= g b) -> (forall a, a <= g a) ->
  forall n x m, n <= m -> x <= m -> iter n g x <= iter m g m.
Proof.
  intros g Hm Hid n x m Hn Hx.
  transitivity (iter n g m); [apply iter_mono_x; assumption |].
  apply iter_mono_n; assumption.
Qed.

Lemma cmp_G1 : forall x k, 8 <= x -> k <= 8 -> x + f_omega (x + k) <= iter 3 f_omega x.
Proof.
  intros x k Hx Hk. cbn [iter].
  pose proof (f_omega_dbl x ltac:(dlia)) as H1.
  pose proof (f_omega_mono (x + k) (f_omega x) ltac:(dlia)) as H2.
  pose proof (f_omega_id (f_omega x)) as H3.
  pose proof (f_omega_dbl (f_omega (f_omega x)) ltac:(dlia)) as H4.
  dlia.
Qed.

Lemma cmp_G3 : forall x, 3 <= x -> iter 3 f_omega x <= f_omega1 x.
Proof. intros x Hx. rewrite cmp_F1_unf. apply iter_mono_n; [apply f_omega_id | exact Hx]. Qed.

Lemma cmp_F1_8x : forall x, 3 <= x -> 8 * x <= f_omega1 x.
Proof.
  intros x Hx. transitivity (iter 3 f_omega x); [| apply cmp_G3; exact Hx].
  cbn [iter].
  pose proof (f_omega_dbl x ltac:(dlia)) as H1.
  pose proof (f_omega_dbl (f_omega x) ltac:(dlia)) as H2.
  pose proof (f_omega_dbl (f_omega (f_omega x)) ltac:(dlia)) as H3.
  dlia.
Qed.

(** ** Upper bounds for M12's maps, in the size measure p + a *)

Definition sz (x : nat * nat) : nat := fst x + snd x.

Lemma cmp_sz : forall x, sz x = fst x + snd x.
Proof. reflexivity. Qed.

Lemma cmp_W_aux : forall j b, BB12_M12.W j b + 3 <= f (S j) (b + 3).
Proof.
  induction j as [| j IH]; intros b.
  - rewrite BB12_M12.W_0, f1. dlia.
  - rewrite BB12_M12.W_S, cmp_iter_M.
    assert (Hi : forall i, iter i (BB12_M12.W j) 2 + 3 <= iter i (f (S j)) 5).
    { induction i as [| i IHi]; cbn [iter]; [dlia |].
      specialize (IH (iter i (BB12_M12.W j) 2)).
      pose proof (f_mono (S j) _ _ IHi). dlia. }
    transitivity (iter (S b) (f (S j)) 5); [exact (Hi (S b)) |].
    rewrite (f_S (S j) (b + 3)).
    assert (E : iter (b + 3) (f (S j)) (b + 3) = iter (S b) (f (S j)) (iter 2 (f (S j)) (b + 3))).
    { rewrite <- iter_add. f_equal. dlia. }
    rewrite E. apply iter_mono_x; [intros u v Huv; apply f_mono; exact Huv |].
    cbn [iter].
    pose proof (f_gt (S j) (b + 3) ltac:(dlia)).
    pose proof (f_gt (S j) (f (S j) (b + 3)) ltac:(dlia)). dlia.
Qed.

Lemma cmp_W : forall j b, BB12_M12.W j b <= f_omega (j + b + 4).
Proof.
  intros j b. pose proof (cmp_W_aux j b) as H0.
  pose proof (f_level_mono (b + 3) (S j) (b + 3) ltac:(dlia)) as H1.
  replace (b + 3 + S j) with (j + b + 4) in H1 by dlia.
  pose proof (f_mono (j + b + 4) (b + 3) (j + b + 4) ltac:(dlia)) as H2.
  rewrite cmp_Fw_unf. dlia.
Qed.

Opaque BB12_M12.W.

Lemma cmp_Kc : forall p a t, p + a <= t -> 8 <= t -> sz (BB12_M12.Kc (p, a)) <= iter 3 f_omega t.
Proof.
  intros p a t Hs Ht. rewrite BB12_M12_bound.Kc_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 1).
  pose proof (f_omega_mono (p - 1 + 1 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)). dlia.
Qed.

Lemma cmp_Kc_it : forall n pa t, sz pa <= t -> 8 <= t ->
  sz (BB12_M12.iter n BB12_M12.Kc pa) <= iter (3 * n) f_omega t.
Proof.
  induction n as [| n IH]; intros pa t Hs Ht.
  - cbn [BB12_M12.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB12_M12.iter].
    specialize (IH pa t Hs Ht).
    destruct (BB12_M12.iter n BB12_M12.Kc pa) as [p a] eqn:E.
    try rewrite E in IH. unfold sz in IH; cbn [fst snd] in IH.
    pose proof (iter_ge f_omega f_omega_id (3 * n) t).
    replace (3 * S n) with (3 + 3 * n) by dlia. rewrite iter_add.
    apply cmp_Kc; dlia.
Qed.

Lemma cmp_Kc_full : forall pb t, sz pb <= t -> 8 <= t -> sz (BB12_M12.Kc_full pb) <= iter 2 f_omega1 t.
Proof.
  intros [p b] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB12_M12_bound.Kc_full_unfold.
  assert (H0 : sz (p - 1, BB12_M12.W (p - 1) 3) <= iter 3 f_omega t).
  { unfold sz; cbn [fst snd].
    pose proof (cmp_W (p - 1) 3).
    pose proof (f_omega_mono (p - 1 + 3 + 4) (t + 6) ltac:(dlia)).
    pose proof (cmp_G1 t 6 ltac:(dlia) ltac:(dlia)). dlia. }
  assert (Ht0 : 8 <= iter 3 f_omega t) by (pose proof (iter_ge f_omega f_omega_id 3 t); dlia).
  pose proof (cmp_Kc_it (b / 2) _ _ H0 Ht0) as H1.
  rewrite <- iter_add in H1.
  eapply Nat.le_trans; [exact H1 |].
  transitivity (f_omega1 (2 * t)).
  - rewrite (cmp_F1_unf (2 * t)). apply cmp_iter_diag; [exact f_omega_mono | exact f_omega_id | dlia | dlia].
  - cbn [iter]. apply f_omega1_mono. pose proof (cmp_F1_8x t ltac:(dlia)). dlia.
Qed.

Lemma cmp_Kd_step : forall pb t, sz pb <= t -> 8 <= t -> sz (BB12_M12.Kd_step pb) <= iter 3 f_omega1 t.
Proof.
  intros pb t Hs Ht. rewrite BB12_M12_bound.Kd_step_unfold.
  pose proof (cmp_Kc_full pb t Hs Ht) as H1.
  destruct (BB12_M12.Kc_full pb) as [p a] eqn:E.
  try rewrite E in H1. unfold sz in H1 |- *; cbn [fst snd] in H1 |- *.
  assert (HT : 8 <= iter 2 f_omega1 t) by (pose proof (iter_ge f_omega1 f_omega1_id 2 t); dlia).
  pose proof (cmp_W p (a + 4)).
  pose proof (f_omega_mono (p + (a + 4) + 4) (iter 2 f_omega1 t + 8) ltac:(dlia)).
  pose proof (cmp_G1 (iter 2 f_omega1 t) 8 ltac:(dlia) ltac:(dlia)).
  pose proof (cmp_G3 (iter 2 f_omega1 t) ltac:(dlia)).
  change (iter 3 f_omega1 t) with (f_omega1 (iter 2 f_omega1 t)).
  dlia.
Qed.

Lemma cmp_Kd_iter : forall m pb t, sz pb <= t -> 8 <= t ->
  sz (BB12_M12.Kd_iter m pb) <= iter (3 * m) f_omega1 t.
Proof.
  intros m pb t Hs Ht. rewrite BB12_M12_bound.Kd_iter_unfold.
  induction m as [| m IH].
  - cbn [BB12_M12.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB12_M12.iter]. replace (3 * S m) with (3 + 3 * m) by dlia. rewrite iter_add.
    apply cmp_Kd_step; [exact IH |].
    pose proof (iter_ge f_omega1 f_omega1_id (3 * m) t). dlia.
Qed.

Lemma cmp_D_reload : forall pa t, sz pa <= t -> 8 <= t -> sz (BB12_M12.D_reload pa) <= f_omega1 t.
Proof.
  intros [p a] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB12_M12_bound.D_reload_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 0).
  pose proof (f_omega_mono (p - 1 + 0 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)).
  pose proof (cmp_G3 t ltac:(dlia)). dlia.
Qed.

(** ** M12's run: one tight f_omega2 at the top *)

(** The last half-round of M12, for variables: one application of f_omega2 (sharper than cmp_stageA). *)
Lemma cmp_round2 : forall pa t, sz pa <= t -> 8 <= t ->
  sz (BB12_M12.Kd_iter (snd pa / 6 + 1) (BB12_M12.D_reload pa)) <= f_omega2 (4 * t).
Proof.
  intros pa t Hs Ht.
  pose proof (cmp_D_reload pa t Hs Ht) as H1.
  assert (H8 : 8 <= f_omega1 t) by (pose proof (f_omega1_id t); dlia).
  pose proof (cmp_Kd_iter (snd pa / 6 + 1) _ _ H1 H8) as H2.
  assert (E : iter (3 * (snd pa / 6 + 1)) f_omega1 (f_omega1 t) = iter (3 * (snd pa / 6 + 1) + 1) f_omega1 t).
  { rewrite iter_add. reflexivity. }
  rewrite E in H2.
  eapply Nat.le_trans; [exact H2 |].
  rewrite (cmp_F2_unf (4 * t)).
  apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | | dlia].
  rewrite cmp_sz in Hs. dlia.
Qed.

Lemma cmp_iter_1 : forall (g : nat -> nat) x, g x = iter 1 g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_iter : forall (g : nat -> nat) a b x, iter a g (iter b g x) = iter (a + b) g x.
Proof. intros. rewrite iter_add. reflexivity. Qed.

Lemma cmp_pa1 : sz BB12_M12.pa1 <= iter (2 + (3 + 1)) f_omega1 12.
Proof.
  rewrite BB12_M12.pa1_def, BB12_M12.pb1_1_def, BB12_M12.pb1_0_def.
  pose proof (cmp_D_reload (8, 4) 12 ltac:(unfold sz; cbn [fst snd]; dlia) ltac:(dlia)) as H1.
  assert (H8 : 8 <= f_omega1 12) by (pose proof (f_omega1_id 12); dlia).
  pose proof (cmp_Kd_step _ _ H1 H8) as H2.
  assert (H8' : 8 <= iter 3 f_omega1 (f_omega1 12))
    by (pose proof (iter_ge f_omega1 f_omega1_id 3 (f_omega1 12)); dlia).
  pose proof (cmp_Kc_full _ _ H2 H8') as H4.
  rewrite (cmp_iter_1 f_omega1 12), !cmp_iter_iter in H4.
  exact H4.
Qed.

Lemma cmp_T1_8 : 8 <= iter (2 + (3 + 1)) f_omega1 12.
Proof. pose proof (iter_ge f_omega1 f_omega1_id (2 + (3 + 1)) 12). dlia. Qed.

Lemma cmp_pb2 : sz BB12_M12.pb2 <= f_omega2 (4 * iter (2 + (3 + 1)) f_omega1 12).
Proof.
  rewrite BB12_M12.pb2_def, BB12_M12.pb2_0_def.
  exact (cmp_round2 BB12_M12.pa1 (iter (2 + (3 + 1)) f_omega1 12) cmp_pa1 cmp_T1_8).
Qed.

Lemma cmp_score_M12 :
  fst BB12_M12.pb2 + snd BB12_M12.pb2 / 2 + 3 <= f_omega2 (4 * iter (2 + (3 + 1)) f_omega1 12) + 3.
Proof. pose proof cmp_pb2 as H. rewrite cmp_sz in H. dlia. Qed.

(** ** The comparison *)

(** 4 * f_omega1^6(12) <= f_omega1^7(12) <= f_omega2 34 <= f_omega2 (f 5 34). *)
Lemma cmp_T1_small : 4 * iter (2 + (3 + 1)) f_omega1 12 <= f_omega2 (f 5 34).
Proof.
  pose proof cmp_T1_8 as H0.
  pose proof (cmp_F1_8x (iter (2 + (3 + 1)) f_omega1 12) ltac:(dlia)) as H1.
  rewrite (cmp_iter_1 f_omega1 (iter (2 + (3 + 1)) f_omega1 12)), cmp_iter_iter in H1.
  assert (H2 : iter (1 + (2 + (3 + 1))) f_omega1 12 <= iter 34 f_omega1 34)
    by (apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | dlia | dlia]).
  rewrite <- cmp_F2_unf in H2.
  pose proof (f_omega2_mono _ _ f34) as H3.
  dlia.
Qed.

(** The last step, for variables. *)
Lemma cmp_final : forall s y z a n, s <= f_omega2 y + 3 -> y <= f_omega2 z -> z <= a ->
  4 * f_omega2 (f_omega2 a) + 8 <= n -> s < n.
Proof.
  intros s y z a n Hs Hy Hz Hn.
  pose proof (f_omega2_mono _ _ Hz) as H1.
  pose proof (f_omega2_mono _ _ (Nat.le_trans _ _ _ Hy (f_omega2_mono _ _ Hz))) as H2.
  dlia.
Qed.

Theorem beats_M12_exact :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ fst BB12_M12.pb2 + snd BB12_M12.pb2 / 2 + 3 < n.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (snd nFIN + 3 + fst nFIN).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof FIN_dom as HF.
  assert (HF' : 4 * f_omega2 (f_omega2 (W 5 (W 2 4) / 4)) + 8 <= snd nFIN + 3 + fst nFIN) by dlia.
  exact (cmp_final _ _ _ _ _ cmp_score_M12 cmp_T1_small a1_ge HF').
Qed.

(** The same, together with M12's exact-score theorem: the number NM of ones on M12's halting tape is smaller
    than the number of ones on C4's halting tape. *)
Theorem beats_M12_score :
  exists NM,
    (exists c, Individual122.Individual122.Permute.Flip.Compute.TM.evstep BB12_M12.tm
                 Individual122.Individual122.Permute.Flip.Compute.TM.c0 c /\
               Individual122.Individual122.Permute.Flip.Compute.TM.halted BB12_M12.tm c /\
               BB12_M12_bound.ones c NM) /\
    (exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ NM < n).
Proof.
  exists (fst BB12_M12.pb2 + snd BB12_M12.pb2 / 2 + 3).
  split; [exact BB12_M12_bound.score_exact | exact beats_M12_exact].
Qed.
