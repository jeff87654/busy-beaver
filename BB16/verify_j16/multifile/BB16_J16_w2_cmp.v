(** Comparisons of J16_w2 (BB16_J16_w2.v) with the entries it supersedes:
    - J15_fw13 (BB(15), BB15_J15_fw13.v):  sigma_lower_bound  f_wk 13 20 < N
    - M14_31   (BB(14), BB14_M14_31.v):    sigma_bound_fw1    n > iter 30 f_omega2 (iter 2 f_omega1 3)
    - M16_C    (BB(16), BB16_M16c_fw3.v):  sigma_lower_bound  f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) < N
    - M17_B    (BB(17), BB17_halt_fw3.v):  sigma_lower_bound  iter 116 f_omega2 (iter 3 f_omega3 9) < N
    Those files define f_omega1 n = iter n f_omega n, f_omega2 n = iter n f_omega1 n, f_omega3 n = iter n f_omega2 n
    over the same iter / f / f_omega as BB16_J16_w2.v (the same text).  They are repeated below and are f_wk 1, 2, 3
    by definition.  J16_w2's halting tape holds more ones than each of these bounds. *)

From BB8 Require Import Individual162.
From BB8 Require Import BB16_J16_w2.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
(* the main file may make the hierarchy opaque at its end; the generic facts below unfold it (abstract arguments only) *)
Transparent f f_omega f_wk f_w2.

(** Generic facts about the file's own [iter], [f], [f_omega], [f_wk] (standard definitions), proved here from
    the definitions only, so that the comparisons below do not depend on the main proof's lemma names. *)

Lemma cmp_iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. intros X a. induction a as [|a IH]; intros b g x; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma cmp_iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg n. induction n as [|n IH]; intros x; simpl; [lia |].
  specialize (IH x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma cmp_iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg n. induction n as [|n IH]; intros x y Hxy; simpl; auto. Qed.

Lemma cmp_iter_mono_n : forall g, (forall a, a <= g a) ->
  forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite cmp_iter_add. apply cmp_iter_ge. exact Hg.
Qed.

Definition cmp_ok (g : nat -> nat) := (forall n, n <= g n) /\ (forall a b, a <= b -> g a <= g b).

Lemma cmp_diag_ok : forall g, cmp_ok g -> cmp_ok (fun n => iter n g n).
Proof.
  intros g [Hid Hmono]. split.
  - intros n. apply cmp_iter_ge. exact Hid.
  - intros a b Hab. eapply Nat.le_trans.
    + apply cmp_iter_mono_x; [exact Hmono | exact Hab].
    + apply cmp_iter_mono_n; [exact Hid | exact Hab].
Qed.

Lemma cmp_diag_step : forall g, cmp_ok g -> forall n, 1 <= n -> g n <= iter n g n.
Proof.
  intros g [Hid Hmono] n Hn. destruct n as [|n]; [lia |]. simpl.
  apply Hmono. apply cmp_iter_ge. exact Hid.
Qed.

(** [iter m g x] with m <= x is at most the next level at x. *)
Lemma cmp_absorb : forall g, cmp_ok g -> forall m x, m <= x -> iter m g x <= iter x g x.
Proof. intros g [Hid _] m x Hm. apply cmp_iter_mono_n; [exact Hid | exact Hm]. Qed.

Lemma cmp_f_ok : forall k, cmp_ok (f k).
Proof.
  induction k as [|k IH].
  - unfold cmp_ok. change (f 0) with S. split; intros; lia.
  - change (cmp_ok (fun n => iter n (f k) n)). apply cmp_diag_ok. exact IH.
Qed.

Lemma cmp_f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. change (f (S k) n) with (iter n (f k) n).
  apply cmp_diag_step; [apply cmp_f_ok | exact Hn].
Qed.

Lemma cmp_f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d as [|d IH]; intros k n Hn; [simpl; lia |].
  replace (S d + k) with (S (d + k)) by lia.
  eapply Nat.le_trans; [apply IH; exact Hn | apply cmp_f_level; exact Hn].
Qed.

Lemma cmp_iter_S : forall n x, iter n S x = n + x.
Proof. induction n as [|n IH]; intros x; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma cmp_f_omega_ok : cmp_ok f_omega.
Proof.
  split.
  - intros n. unfold f_omega. apply (proj1 (cmp_f_ok n)).
  - intros a b Hab. unfold f_omega. destruct b as [|b].
    + assert (a = 0) by lia. subst. lia.
    + eapply Nat.le_trans; [apply (proj2 (cmp_f_ok a)); exact Hab |].
      pose proof (cmp_f_level_mono (S b - a) a (S b)) as Hl.
      replace (S b - a + a) with (S b) in Hl by lia. apply Hl. lia.
Qed.

Lemma cmp_f_omega_ge2 : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof.
  intros n Hn. unfold f_omega.
  assert (H1 : f 1 n = 2 * n). { change (f 1 n) with (iter n S n). rewrite cmp_iter_S. lia. }
  pose proof (cmp_f_level_mono (n - 1) 1 n Hn) as Hl.
  replace (n - 1 + 1) with n in Hl by lia. lia.
Qed.

Lemma cmp_f_wk_ok : forall k, cmp_ok (f_wk k).
Proof.
  induction k as [|k IH].
  - exact cmp_f_omega_ok.
  - change (cmp_ok (fun n => iter n (f_wk k) n)). apply cmp_diag_ok. exact IH.
Qed.

Lemma cmp_f_wk_id : forall k n, n <= f_wk k n.
Proof. intros k. exact (proj1 (cmp_f_wk_ok k)). Qed.

Lemma cmp_f_wk_mono : forall k a b, a <= b -> f_wk k a <= f_wk k b.
Proof. intros k. exact (proj2 (cmp_f_wk_ok k)). Qed.

Lemma cmp_f_wk_level : forall k n, 1 <= n -> f_wk k n <= f_wk (S k) n.
Proof.
  intros k n Hn. change (f_wk (S k) n) with (iter n (f_wk k) n).
  apply cmp_diag_step; [apply cmp_f_wk_ok | exact Hn].
Qed.

Lemma cmp_f_wk_level_mono : forall d k n, 1 <= n -> f_wk k n <= f_wk (d + k) n.
Proof.
  induction d as [|d IH]; intros k n Hn; [simpl; lia |].
  replace (S d + k) with (S (d + k)) by lia.
  eapply Nat.le_trans; [apply IH; exact Hn | apply cmp_f_wk_level; exact Hn].
Qed.

Lemma cmp_f_wk_ge2 : forall k n, 1 <= n -> 2 * n <= f_wk k n.
Proof.
  intros k n Hn. eapply Nat.le_trans; [apply cmp_f_omega_ge2; exact Hn |].
  pose proof (cmp_f_wk_level_mono k 0 n Hn) as Hl. rewrite Nat.add_0_r in Hl. exact Hl.
Qed.

(** [iter m (f_wk k) x] with m <= x is at most f_(omega+k+1)(x). *)
Lemma cmp_wk_absorb : forall k m x, m <= x -> iter m (f_wk k) x <= f_wk (S k) x.
Proof. intros k m x Hm. change (f_wk (S k) x) with (iter x (f_wk k) x). apply cmp_absorb; [apply cmp_f_wk_ok | exact Hm]. Qed.

(** f_(omega+k)(x) <= f_(omega*2)(y) when k <= y and x <= y. *)
Lemma cmp_wk_le_w2 : forall k x y, k <= y -> x <= y -> 1 <= y -> f_wk k x <= f_wk y y.
Proof.
  intros k x y Hk Hx Hy. eapply Nat.le_trans; [apply cmp_f_wk_mono; exact Hx |].
  pose proof (cmp_f_wk_level_mono (y - k) k y Hy) as Hl. replace (y - k + k) with y in Hl by lia. exact Hl.
Qed.

Lemma cmp_wk_S_eq : forall k n, f_wk (S k) n = iter n (f_wk k) n.
Proof. reflexivity. Qed.

Lemma cmp_f_omega_eq : forall n, f_omega n = f n n.
Proof. reflexivity. Qed.

Lemma cmp_iter_S_r : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. intros X n. induction n as [|n IH]; intros g x; [reflexivity |]. simpl. now rewrite <- IH. Qed.

Lemma cmp_iter_1 : forall {X : Type} (g : X -> X) x, iter 1 g x = g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_2 : forall {X : Type} (g : X -> X) x, iter 2 g x = g (g x).
Proof. reflexivity. Qed.

Lemma cmp_iter_3 : forall {X : Type} (g : X -> X) x, iter 3 g x = g (g (g x)).
Proof. reflexivity. Qed.

Lemma cmp_iter_4 : forall {X : Type} (g : X -> X) x, iter 4 g x = g (g (g (g x))).
Proof. reflexivity. Qed.

Lemma cmp_iter_ext : forall (g h : nat -> nat), (forall y, g y = h y) -> forall n x, iter n g x = iter n h x.
Proof. intros g h E n. induction n as [|n IH]; intros x; simpl; [reflexivity | now rewrite IH, E]. Qed.

Lemma cmp_wk_twice : forall k x, 2 <= x -> f_wk k (f_wk k x) <= f_wk (S k) x.
Proof. intros k x Hx. rewrite <- (cmp_iter_2 (f_wk k) x). apply cmp_wk_absorb. exact Hx. Qed.

Lemma cmp_wk_four : forall k x, 4 <= x -> f_wk k (f_wk k (f_wk k (f_wk k x))) <= f_wk (S k) x.
Proof. intros k x Hx. rewrite <- (cmp_iter_4 (f_wk k) x). apply cmp_wk_absorb. exact Hx. Qed.

(** iter n (f_(omega+k)) (f_(omega+k)(x)) <= f_(omega+k+1)(y) when n + 1 <= y and x <= y. *)
Lemma cmp_wk_shift_absorb : forall k n x y, S n <= y -> x <= y ->
  iter n (f_wk k) (f_wk k x) <= f_wk (S k) y.
Proof.
  intros k n x y Hn Hx. rewrite <- cmp_iter_S_r.
  apply Nat.le_trans with (iter (S n) (f_wk k) y); [apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact Hx] |].
  apply cmp_wk_absorb. exact Hn.
Qed.

Lemma cmp_f_w2_eq : forall n, f_w2 n = f_wk n n.
Proof. reflexivity. Qed.

Lemma cmp_f_w2_mono : forall a b, a <= b -> f_w2 a <= f_w2 b.
Proof.
  intros a b Hab. rewrite !cmp_f_w2_eq. destruct b as [|b]; [assert (a = 0) by lia; subst; lia |].
  apply cmp_wk_le_w2; lia.
Qed.

(** The f_(omega+k) notation of BB14_M14_31.v / BB16_M16c_fw3.v / BB17_halt_fw3.v (the same text there). *)
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.
Definition f_omega3 (n : nat) : nat := iter n f_omega2 n.

Lemma f_omega1_wk : forall n, f_omega1 n = f_wk 1 n.
Proof. reflexivity. Qed.
Lemma f_omega2_wk : forall n, f_omega2 n = f_wk 2 n.
Proof. reflexivity. Qed.
Lemma f_omega3_wk : forall n, f_omega3 n = f_wk 3 n.
Proof. reflexivity. Qed.

Lemma iter_o1 : forall n x, iter n f_omega1 x = iter n (f_wk 1) x.
Proof. apply cmp_iter_ext. exact f_omega1_wk. Qed.
Lemma iter_o2 : forall n x, iter n f_omega2 x = iter n (f_wk 2) x.
Proof. apply cmp_iter_ext. exact f_omega2_wk. Qed.
Lemma iter_o3 : forall n x, iter n f_omega3 x = iter n (f_wk 3) x.
Proof. apply cmp_iter_ext. exact f_omega3_wk. Qed.

Lemma f3_2 : f 3 2 = 2048.
Proof. vm_compute. reflexivity. Qed.

Opaque f f_omega f_wk f_w2 f_omega1 f_omega2 f_omega3.

(** M14_31's bound is below f_(omega+13)(20). *)
Lemma M14_31_bound_le : iter 30 f_omega2 (iter 2 f_omega1 3) <= f_wk 13 20.
Proof.
  rewrite iter_o1, iter_o2.
  assert (H31 : 31 <= f_wk 3 20) by (pose proof (cmp_f_wk_ge2 3 20 ltac:(lia)); lia).
  assert (HX : iter 2 (f_wk 1) 3 <= f_wk 2 20).
  { rewrite cmp_wk_S_eq.
    apply Nat.le_trans with (iter 2 (f_wk 1) 20).
    - apply cmp_iter_mono_x; [apply cmp_f_wk_mono | lia].
    - apply cmp_iter_mono_n; [apply cmp_f_wk_id | lia]. }
  apply Nat.le_trans with (iter 30 (f_wk 2) (f_wk 2 20)).
  { apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact HX]. }
  apply Nat.le_trans with (f_wk 3 (f_wk 3 20)).
  { apply cmp_wk_shift_absorb; lia. }
  apply Nat.le_trans with (f_wk 4 20).
  { apply cmp_wk_twice. lia. }
  pose proof (cmp_f_wk_level_mono 9 4 20 ltac:(lia)) as Hl. simpl (9 + 4) in Hl. exact Hl.
Qed.

Lemma Y_big : 2048 <= f 15 2.
Proof.
  rewrite <- f3_2. pose proof (cmp_f_level_mono 12 3 2 ltac:(lia)) as Hl. simpl (12 + 3) in Hl. exact Hl.
Qed.

Lemma wk_le_Y : forall k x, k <= 2048 -> x <= 2048 -> f_wk k x <= f_w2 (f 15 2).
Proof. intros k x Hk Hx. pose proof Y_big. rewrite cmp_f_w2_eq. apply cmp_wk_le_w2; lia. Qed.

Lemma B_big : 232 <= f_wk 4 116.
Proof. pose proof (cmp_f_wk_ge2 4 116 ltac:(lia)). lia. Qed.

Lemma M17_B_bound_le : iter 116 f_omega2 (iter 3 f_omega3 9) <= f_w2 (f 15 2).
Proof.
  rewrite iter_o3, iter_o2.
  pose proof B_big as HB.
  assert (HA : iter 3 (f_wk 3) 9 <= f_wk 4 116).
  { rewrite (cmp_wk_S_eq 3 116).
    apply Nat.le_trans with (iter 3 (f_wk 3) 116).
    - apply cmp_iter_mono_x; [apply cmp_f_wk_mono | lia].
    - apply cmp_iter_mono_n; [apply cmp_f_wk_id | lia]. }
  apply Nat.le_trans with (iter 116 (f_wk 2) (f_wk 4 116)).
  { apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact HA]. }
  apply Nat.le_trans with (f_wk 3 (f_wk 4 116)).
  { apply cmp_wk_absorb. lia. }
  apply Nat.le_trans with (f_wk 4 (f_wk 4 116)).
  { apply cmp_f_wk_level. lia. }
  apply Nat.le_trans with (f_wk 5 116).
  { apply cmp_wk_twice. lia. }
  apply wk_le_Y; lia.
Qed.

Lemma M16_C_bound_le : f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) <= f_w2 (f 15 2).
Proof.
  rewrite f_omega3_wk, iter_o2, iter_o1, f_omega2_wk.
  pose proof B_big as HB.
  assert (H1 : f_wk 3 9 <= f_wk 4 116).
  { apply Nat.le_trans with (f_wk 3 116); [apply cmp_f_wk_mono; lia |]. apply cmp_f_wk_level. lia. }
  assert (HD : f_wk 4 116 <= f_wk 4 (f_wk 4 116)) by apply cmp_f_wk_id.
  assert (H2 : iter 3 (f_wk 2) (f_wk 3 9) <= f_wk 4 (f_wk 4 116)).
  { apply Nat.le_trans with (iter 3 (f_wk 2) (f_wk 4 116)).
    { apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact H1]. }
    apply Nat.le_trans with (f_wk 3 (f_wk 4 116)); [apply cmp_wk_absorb; lia |].
    apply cmp_f_wk_level. lia. }
  assert (HE : f_wk 4 (f_wk 4 116) <= f_wk 4 (f_wk 4 (f_wk 4 116))) by apply cmp_f_wk_id.
  assert (H3 : iter 114 (f_wk 1) (iter 3 (f_wk 2) (f_wk 3 9)) <= f_wk 4 (f_wk 4 (f_wk 4 116))).
  { apply Nat.le_trans with (iter 114 (f_wk 1) (f_wk 4 (f_wk 4 116))).
    { apply cmp_iter_mono_x; [apply cmp_f_wk_mono | exact H2]. }
    apply Nat.le_trans with (f_wk 2 (f_wk 4 (f_wk 4 116))); [apply cmp_wk_absorb; lia |].
    pose proof (cmp_f_wk_level_mono 2 2 (f_wk 4 (f_wk 4 116)) ltac:(lia)) as Hl. simpl (2 + 2) in Hl. exact Hl. }
  assert (HF : f_wk 4 (f_wk 4 (f_wk 4 116)) <= f_wk 4 (f_wk 4 (f_wk 4 (f_wk 4 116)))) by apply cmp_f_wk_id.
  apply Nat.le_trans with (f_wk 2 (f_wk 4 (f_wk 4 (f_wk 4 116)))); [apply cmp_f_wk_mono; exact H3 |].
  apply Nat.le_trans with (f_wk 4 (f_wk 4 (f_wk 4 (f_wk 4 116)))).
  { pose proof (cmp_f_wk_level_mono 2 2 (f_wk 4 (f_wk 4 (f_wk 4 116))) ltac:(lia)) as Hl.
    simpl (2 + 2) in Hl. exact Hl. }
  apply Nat.le_trans with (f_wk 5 116).
  { apply cmp_wk_four. lia. }
  apply wk_le_Y; lia.
Qed.

Theorem beats_J15 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 13 20 < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (wk_le_Y 13 20 ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem beats_M14_31 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 30 f_omega2 (iter 2 f_omega1 3) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof M14_31_bound_le. pose proof (wk_le_Y 13 20 ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem beats_M16_C :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
    f_omega2 (iter 114 f_omega1 (iter 3 f_omega2 (f_omega3 9))) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof M16_C_bound_le. lia.
Qed.

Theorem beats_M17_B :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 116 f_omega2 (iter 3 f_omega3 9) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4 & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof M17_B_bound_le. lia.
Qed.
